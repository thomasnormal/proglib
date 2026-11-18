#!/usr/bin/env python3
"""Check the reactive dependency wall against canonical E and both simulators."""

from __future__ import annotations

from pathlib import Path
import hashlib
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
SOURCE = HERE / "reactive_backward.sv"
TB = HERE / "reactive_backward_tb.sv"
EXPECTED = [
    "ROW t=0 a=0 y=x",
    "ROW t=2 a=1 y=1",
    "ROW t=3 a=1 y=1",
]
SOURCE_SHA256 = "96b39580c3a89453c4a910af6550bf54670d9af2e26aaa92ff9a9f720d78d7a8"
ENVELOPE = HERE / "reactive_backward.sv.json"
ENVELOPE_SHA256 = "05eb311317802d4f4ab3ee3591998ea2cc63bf8236e79cb2e73c3bb4c216dbe2"
REFUSAL = (
    "Comb:dependency-order: 9.2.2.2/9.4.2.2: reactive process reads 't' "
    "from itself or a later reactive process; canonical E has no fixed-point scheduler"
)


def run(command: list[str], cwd: Path) -> str:
    result = subprocess.run(
        command,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
        timeout=180,
    )
    if result.returncode:
        raise RuntimeError("command failed: %s\n%s" % (" ".join(command), result.stdout))
    return result.stdout


def rows(output: str) -> list[str]:
    return [line.strip() for line in output.splitlines() if line.startswith("ROW ")]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    if sha256(SOURCE) != SOURCE_SHA256:
        raise RuntimeError("reactive wall source hash does not match the pinned fixture")
    if sha256(ENVELOPE) != ENVELOPE_SHA256:
        raise RuntimeError("reactive wall envelope hash does not match the pinned fixture")
    print("source SHA-256: " + SOURCE_SHA256)
    print("envelope SHA-256: " + ENVELOPE_SHA256)
    e_output = run(["lake", "env", "lean", str(HERE / "reactive_backward_probe.lean")], ROOT)
    if "reactive_backward_probe" not in e_output and e_output.strip():
        raise RuntimeError("unexpected canonical-E probe output:\n" + e_output)
    print("canonical E: exact reactive dependency-order refusal")

    if shutil.which("iverilog") is None or shutil.which("vvp") is None:
        raise RuntimeError("Icarus Verilog 13.0 is required")
    if shutil.which("xrun") is None:
        raise RuntimeError("Xcelium 24.03-s004 is required")

    iverilog_version = run(["iverilog", "-V"], ROOT)
    if "Icarus Verilog version 13.0" not in iverilog_version:
        raise RuntimeError("unexpected Icarus version:\n" + iverilog_version)
    xrun_version = run(["xrun", "-version"], ROOT)
    if "24.03-s004" not in xrun_version:
        raise RuntimeError("unexpected Xcelium version:\n" + xrun_version)

    with tempfile.TemporaryDirectory(prefix="sv-reactive-backward-") as work:
        directory = Path(work)
        executable = directory / "sim"
        run(["iverilog", "-g2012", "-s", "reactive_backward_tb",
             "-o", str(executable), str(SOURCE), str(TB)], directory)
        actual = rows(run(["vvp", str(executable)], directory))
        if actual != EXPECTED:
            raise RuntimeError("Icarus rows: %r" % actual)
    print("Icarus Verilog 13.0 (s20250103-64-gdad78d525): 3 rows MATCH")

    with tempfile.TemporaryDirectory(prefix="sv-reactive-backward-xcelium-") as work:
        directory = Path(work)
        actual = rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                           "-top", "reactive_backward_tb", str(SOURCE), str(TB)], directory))
        if actual != EXPECTED:
            raise RuntimeError("Xcelium rows: %r" % actual)
    print("Xcelium 24.03-s004: 3 rows MATCH")
    print("wall: " + REFUSAL)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
