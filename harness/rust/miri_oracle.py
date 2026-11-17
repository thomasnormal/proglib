#!/usr/bin/env python3
"""Run one Rust program under the pinned Miri oracle.

The program argument is either a standalone ``.rs`` file or a Cargo
``Cargo.toml``.  A source file is copied into a temporary, dependency-free
binary crate; the source itself is never inspected or re-parsed.  Each input
is run twice: Miri's default Stacked Borrows model and its Tree Borrows model.

The output is one JSON document with the exact toolchain, Miri flags, command,
exit status, raw output, and a conservative runtime verdict for each model.
Use ``--self-test`` to run the four checked-in fixtures covering return,
explicit exit, panic, and undefined behavior.

The harness requires the lane-local ``RUSTUP_HOME``, ``CARGO_HOME``, and
``TMPDIR``.  ``MIRI_SYSROOT`` may point at the generated sysroot; when it is
omitted, ``$RUST_LANE_ROOT/miri-cache/<pinned-toolchain>`` is used.
"""

import argparse
import json
import os
import re
import shutil
import signal
import subprocess
import sys
import tempfile
from pathlib import Path


TOOLCHAIN = "nightly-2026-11-16"
TOOLCHAIN_TRIPLE = "nightly-2026-11-16-x86_64-unknown-linux-gnu"
RUSTC_VERSION = "1.102.0-nightly (5f4effd57 2026-11-13)"
CARGO_VERSION = "1.102.0-nightly (ede6cefea 2026-11-11)"
MIRI_VERSION = "0.1.0 (5f4effd579 2026-11-13)"
MIRI_FLAGS = (
    "-Zmiri-deterministic-concurrency",
    "-Zmiri-deterministic-floats",
    "-Zmiri-seed=0",
    "-Zmiri-num-cpus=1",
    "-Zmiri-isolation-error=abort",
)
UB_MARKER = "Undefined Behavior:"
PANIC_RE = re.compile(r"(?:thread '[^']+'|panicked at)")
COMPILER_ERROR_RE = re.compile(r"(?m)^(?:error(?:\[[^]]+\])?:|error:|could not compile)")


class HarnessError(Exception):
    """A setup or command failure, distinct from a program verdict."""


def _required_environment():
    missing = [name for name in ("RUSTUP_HOME", "CARGO_HOME", "TMPDIR")
               if not os.environ.get(name)]
    if missing:
        raise HarnessError("missing lane-local environment: " + ", ".join(missing))


def _rustup():
    path = shutil.which("rustup")
    if path is None:
        raise HarnessError("rustup is not on PATH")
    return path


def _sysroot():
    configured = os.environ.get("MIRI_SYSROOT")
    if configured:
        candidate = Path(configured).expanduser()
    else:
        lane_root = os.environ.get("RUST_LANE_ROOT")
        if not lane_root:
            raise HarnessError("set MIRI_SYSROOT or RUST_LANE_ROOT")
        candidate = Path(lane_root) / "miri-cache" / TOOLCHAIN_TRIPLE
    if not (candidate / "lib" / "rustlib").is_dir():
        raise HarnessError("MIRI_SYSROOT is not a generated Miri sysroot: " +
                           str(candidate))
    return candidate.resolve()


def _work_root(argument):
    value = argument or os.environ.get("RUST_LANE_ROOT")
    if not value:
        raise HarnessError("pass --work-root or set RUST_LANE_ROOT")
    root = Path(value).expanduser().resolve() / "miri-oracle-work"
    root.mkdir(parents=True, exist_ok=True)
    return root


def _capture(command, env):
    completed = subprocess.run(command, env=env, stdout=subprocess.PIPE,
                               stderr=subprocess.PIPE, universal_newlines=True,
                               check=False)
    return completed.returncode, completed.stdout, completed.stderr


def _toolchain_info(rustup, env):
    rustc_status, rustc_out, rustc_err = _capture(
        [rustup, "run", TOOLCHAIN, "rustc", "--version", "--verbose"], env)
    if rustc_status != 0:
        raise HarnessError("rustc --version failed: " + rustc_err.strip())
    cargo_status, cargo_out, cargo_err = _capture(
        [rustup, "run", TOOLCHAIN, "cargo", "--version"], env)
    if cargo_status != 0:
        raise HarnessError("cargo --version failed: " + cargo_err.strip())
    miri_status, miri_out, miri_err = _capture(
        [rustup, "run", TOOLCHAIN, "cargo", "miri", "--version"], env)
    if miri_status != 0:
        raise HarnessError("cargo miri --version failed: " + miri_err.strip())
    if not rustc_out.startswith("rustc " + RUSTC_VERSION + "\n"):
        raise HarnessError("unexpected rustc version: " + rustc_out.splitlines()[0])
    if not cargo_out.startswith("cargo " + CARGO_VERSION + "\n"):
        raise HarnessError("unexpected cargo version: " + cargo_out.strip())
    if not miri_out.startswith("miri " + MIRI_VERSION + "\n"):
        raise HarnessError("unexpected Miri version: " + miri_out.strip())
    return {
        "channel": TOOLCHAIN_TRIPLE,
        "rustc": rustc_out.strip(),
        "cargo": cargo_out.strip(),
        "miri": miri_out.strip(),
        "pinned_versions": {
            "rustc": RUSTC_VERSION,
            "cargo": CARGO_VERSION,
            "miri": MIRI_VERSION,
        },
    }


def _base_environment(sysroot, flags, target_dir):
    env = os.environ.copy()
    env["MIRI_SYSROOT"] = str(sysroot)
    env["MIRIFLAGS"] = " ".join(flags)
    env["CARGO_TARGET_DIR"] = str(target_dir)
    env["CARGO_TERM_COLOR"] = "never"
    env["CARGO_INCREMENTAL"] = "0"
    # Miri isolation deliberately hides host variables from the interpreted
    # program.  This value only controls an outer panic diagnostic.
    env["RUST_BACKTRACE"] = "0"
    return env


def _run(command, env, cwd, timeout):
    process = subprocess.Popen(command, cwd=str(cwd), env=env,
                               stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                               universal_newlines=True, start_new_session=True)
    try:
        stdout, stderr = process.communicate(timeout=timeout)
        return process.returncode, False, stdout, stderr
    except subprocess.TimeoutExpired as error:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except (OSError, ProcessLookupError):
            process.kill()
        stdout, stderr = process.communicate()
        # communicate() can return the partial strings carried by the timeout
        # exception only on older Python versions; use the completed streams
        # when available and append nothing guessed by the harness.
        if not stdout and error.stdout:
            stdout = error.stdout
        if not stderr and error.stderr:
            stderr = error.stderr
        if isinstance(stdout, bytes):
            stdout = stdout.decode("utf-8", "replace")
        if isinstance(stderr, bytes):
            stderr = stderr.decode("utf-8", "replace")
        return None, True, stdout or "", stderr or ""


def _verdict(status, timed_out, stdout, stderr):
    """Classify only Miri's explicit runtime diagnostics.

    A nonzero result without a recognized panic/UB marker is an explicit exit
    only when Miri emitted no diagnostic. This keeps compilation failures,
    unsupported shims, and newly changed diagnostics from being mistaken for a
    successful or unsafe execution.
    """
    if timed_out:
        return "timeout", False, False
    if UB_MARKER in stderr:
        return "ub", False, True
    if PANIC_RE.search(stderr):
        return "panic", True, False
    if status == 0:
        return "ok", False, False
    if status is None or status < 0:
        return "tool_error", False, False
    if not COMPILER_ERROR_RE.search(stderr):
        return "exit", False, False
    return "tool_error", False, False


def _prepare_program(program, work_root):
    path = Path(program).expanduser().resolve()
    if path.is_dir():
        path = path / "Cargo.toml"
    if path.name == "Cargo.toml":
        if not path.is_file():
            raise HarnessError("manifest does not exist: " + str(path))
        return path, path.parent, None
    if path.suffix != ".rs" or not path.is_file():
        raise HarnessError("program must be a .rs file or Cargo.toml: " + str(path))

    project = Path(tempfile.mkdtemp(prefix="source-", dir=str(work_root)))
    source_dir = project / "src"
    source_dir.mkdir()
    shutil.copyfile(str(path), str(source_dir / "main.rs"))
    (project / "Cargo.toml").write_text(
        "[package]\nname = \"lean_surfaces_rust_oracle\"\n"
        "version = \"0.0.0\"\nedition = \"2024\"\n",
        encoding="utf-8",
    )
    return project / "Cargo.toml", project, project


def run_program(program, work_root, timeout, program_args, package=None, binary=None):
    _required_environment()
    rustup = _rustup()
    sysroot = _sysroot()
    work_root.mkdir(parents=True, exist_ok=True)
    manifest, cwd, source_cleanup = _prepare_program(program, work_root)
    run_root = Path(tempfile.mkdtemp(prefix="run-", dir=str(work_root)))
    common = [rustup, "run", TOOLCHAIN, "cargo", "miri", "run",
              "--manifest-path", str(manifest), "--offline", "--quiet"]
    if package:
        common.extend(["--package", package])
    if binary:
        common.extend(["--bin", binary])
    if program_args:
        if program_args[0] == "--":
            program_args = program_args[1:]
    if program_args:
        common.append("--")
        common.extend(program_args)

    runs = []
    try:
        # Query versions once, with the same sysroot and lane environment used
        # for both executions.
        info_env = _base_environment(sysroot, MIRI_FLAGS, run_root / "versions")
        info = _toolchain_info(rustup, info_env)
        for model, extra in (("stacked_borrows", ()),
                             ("tree_borrows", ("-Zmiri-tree-borrows",))):
            flags = MIRI_FLAGS + extra
            target_dir = run_root / model
            target_dir.mkdir(parents=True, exist_ok=True)
            env = _base_environment(sysroot, flags, target_dir)
            command = common[:]
            command[command.index("--quiet"):command.index("--quiet")] = [
                "--target-dir", str(target_dir)
            ]
            status, timed_out, stdout, stderr = _run(command, env, cwd, timeout)
            verdict, panic, ub = _verdict(status, timed_out, stdout, stderr)
            runs.append({
                "model": model,
                "flags": list(flags),
                "command": command,
                "exit_status": status,
                "timed_out": timed_out,
                "panic": panic,
                "ub": ub,
                "verdict": verdict,
                "stdout": stdout,
                "stderr": stderr,
            })
        return {
            "schema": "lean-surfaces.rust.miri-oracle.v0",
            "toolchain": info,
            "program": str(Path(program).expanduser().resolve()),
            "miri_flags": list(MIRI_FLAGS),
            "borrow_models": ["stacked_borrows", "tree_borrows"],
            "runs": runs,
        }
    finally:
        shutil.rmtree(str(run_root), ignore_errors=True)
        if source_cleanup is not None:
            shutil.rmtree(str(source_cleanup), ignore_errors=True)


def _self_test(work_root, timeout):
    fixture_dir = Path(__file__).resolve().parent / "fixtures"
    expected = {
        "ok.rs": "ok",
        "exit.rs": "exit",
        "panic.rs": "panic",
        "ub.rs": "ub",
    }
    summary = []
    for name, wanted in expected.items():
        report = run_program(fixture_dir / name, work_root, timeout, [])
        verdicts = {run["model"]: run["verdict"] for run in report["runs"]}
        if name == "exit.rs":
            if any(run["exit_status"] != 7 for run in report["runs"]):
                raise HarnessError(name + ": expected exit status 7")
            if any(verdict != wanted for verdict in verdicts.values()):
                raise HarnessError(name + ": expected " + wanted + ", got " +
                                   repr(verdicts))
        elif any(verdict != wanted for verdict in verdicts.values()):
            raise HarnessError(name + ": expected " + wanted + ", got " +
                               repr(verdicts))
        summary.append({"program": name, "verdicts": verdicts,
                        "exit_statuses": {run["model"]: run["exit_status"]
                                           for run in report["runs"]}})
    print(json.dumps({"self_test": "pass", "results": summary}, indent=2,
                     sort_keys=True))


def _parser():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("program", nargs="?",
                        help="standalone .rs file, Cargo.toml, or crate directory")
    parser.add_argument("program_args", nargs="*",
                        help="arguments after -- passed to the interpreted binary")
    parser.add_argument("--output", type=Path,
                        help="write the JSON report to this path as well as stdout")
    parser.add_argument("--work-root", type=Path,
                        help="lane-local scratch root (default: $RUST_LANE_ROOT/miri-oracle-work)")
    parser.add_argument("--timeout", type=float, default=120.0,
                        help="seconds per borrow model (default: 120)")
    parser.add_argument("--package", help="Cargo package passed to cargo miri run")
    parser.add_argument("--bin", dest="binary", help="Cargo binary passed to cargo miri run")
    parser.add_argument("--self-test", action="store_true",
                        help="run the checked-in return/exit/panic/UB fixtures")
    return parser


def main(argv=None):
    args = _parser().parse_args(argv)
    try:
        work_root = _work_root(args.work_root)
        if args.timeout <= 0:
            raise HarnessError("--timeout must be positive")
        if args.self_test:
            if args.program:
                raise HarnessError("--self-test does not take a program")
            _self_test(work_root, args.timeout)
            return 0
        if not args.program:
            raise HarnessError("pass a program or --self-test")
        report = run_program(args.program, work_root, args.timeout,
                             args.program_args, package=args.package,
                             binary=args.binary)
        encoded = json.dumps(report, indent=2, sort_keys=True) + "\n"
        if args.output:
            args.output.parent.mkdir(parents=True, exist_ok=True)
            args.output.write_text(encoded, encoding="utf-8")
        sys.stdout.write(encoded)
        return 0 if all(run["verdict"] != "tool_error"
                        for run in report["runs"]) else 2
    except HarnessError as error:
        print("miri_oracle: REFUSE: " + str(error), file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
