#!/usr/bin/env python3
"""Run one unchanged C source through the pinned oracle and C evaluator.

The source is supplied by the caller.  The runner compiles that source,
extracts its parser envelope, and evaluates the same envelope with
``c-torture-run``.  It is intentionally separate from the inline-case
runner so a real source file cannot be replaced by a hand-written twin.
"""

from __future__ import print_function

import argparse
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
PINNED_VERSION = "clang version 21.1.8 (https://github.com/conda-forge/clangdev-feedstock 334cf9a5e6c0331e9f261eaf01fc3568724fcce9)"


def run(command, *, cwd=None, env=None, timeout=180):
    return subprocess.run(command, cwd=str(cwd) if cwd else None, env=env,
                          text=True, capture_output=True, timeout=timeout)


def compiler():
    requested = os.environ.get("LEAN_C_CLANG", "clang")
    executable = (shutil.which(requested)
                  if os.path.basename(requested) == requested else requested)
    if not executable or not Path(executable).exists():
        raise RuntimeError("set LEAN_C_CLANG to the pinned compiler")
    version = run([executable, "--version"], timeout=30)
    first = version.stdout.splitlines()[0] if version.stdout else ""
    if version.returncode != 0 or first != PINNED_VERSION:
        raise RuntimeError("expected %s, got %s" % (PINNED_VERSION, first or "<none>"))
    return executable, first


def evaluate(source, fuel):
    clang, version = compiler()
    source = Path(source).resolve()
    if not source.is_file():
        raise RuntimeError("source does not exist: %s" % source.name)
    with tempfile.TemporaryDirectory(prefix="c-real-program-") as temporary:
        work = Path(temporary)
        native_binary = work / "native"
        native_build = run([
            clang, "--no-default-config", "-std=c23", "-O0", "-g",
            "-D_FORTIFY_SOURCE=0", "-fno-strict-aliasing", str(source),
            "-o", str(native_binary)
        ], timeout=180)
        if native_build.returncode != 0:
            raise RuntimeError("native compile failed: %s" % native_build.stderr[-800:])
        native = run([str(native_binary)], timeout=180)

        envelope = work / "program.json"
        extracted = run([
            sys.executable, str(ROOT / "extractors" / "c" / "extract.py"),
            str(source), "-o", str(envelope)
        ], env=dict(os.environ, LEAN_C_CLANG=clang), timeout=180)
        if extracted.returncode != 0:
            raise RuntimeError("extraction failed: %s" % extracted.stderr[-800:])

        runner = ROOT / ".lake" / "build" / "bin" / "c-torture-run"
        command = [str(runner)] if runner.exists() else ["lake", "exe", "c-torture-run"]
        model = run(command + ["--single", str(envelope), str(fuel)],
                    env=dict(os.environ, LEAN_C_CLANG=clang), timeout=300)
        if model.returncode != 0:
            raise RuntimeError("model refused: %s" % (model.stderr or model.stdout)[-800:])
        marker = model.stdout.rfind("ok\t")
        if marker < 0:
            raise RuntimeError("model produced no score: %s" % model.stdout[-800:])
        model_value = int(model.stdout[marker:].splitlines()[0].split("\t", 1)[1])
        native_value = native.returncode if native.returncode >= 0 else None
        result = {
            "source": source.name,
            "compiler": version,
            "native_exit": native_value,
            "model_exit": model_value,
            "native_stdout": native.stdout,
            "model_stdout": model.stdout,
            "match": native_value == (model_value % 256),
        }
        return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path)
    parser.add_argument("--fuel", type=int, default=1000000)
    args = parser.parse_args()
    try:
        result = evaluate(args.source, args.fuel)
    except (OSError, RuntimeError, ValueError, subprocess.TimeoutExpired) as error:
        print("c_real_program: %s" % error, file=sys.stderr)
        return 2
    print(json.dumps(result, sort_keys=True))
    return 0 if result["match"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
