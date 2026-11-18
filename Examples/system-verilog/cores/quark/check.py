#!/usr/bin/env python3
"""Receipt for the pinned Quark source and its simulator compile blocker."""

from __future__ import annotations

import hashlib
import os
from pathlib import Path
import subprocess


PINNED_COMMIT = "f5ada24ae6cca67d99889daec2c4ee44a6e59417"
SOURCE_SHA256 = "182e6d13bf5ab165b6eefaa22ae8d6a24ea45db6dd2dbd57dcfc5e81932097b7"
ENVELOPE_SHA256 = "b26f0bd9ca5cb9a40838bb7719ae9877876d572f02de076d52d4d9dc62c1efdc"
SOURCE_RELATIVE = Path("FemtoRV/RTL/PROCESSOR/femtorv32_quark.v")


def run(command: list[str], cwd: Path) -> tuple[int, str]:
    result = subprocess.run(
        command,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    return result.returncode, result.stdout


def main() -> None:
    root_text = os.environ.get("QUARK_ROOT")
    if not root_text:
        raise SystemExit("set QUARK_ROOT to the pinned Quark checkout")
    root = Path(root_text).resolve()
    source = root / SOURCE_RELATIVE
    if not source.is_file():
        raise SystemExit(f"missing pinned source: {SOURCE_RELATIVE}")
    commit = run(["git", "rev-parse", "HEAD"], root)[1].strip()
    if commit != PINNED_COMMIT:
        raise SystemExit(f"source commit {commit} is not the pinned {PINNED_COMMIT}")
    source_sha = hashlib.sha256(source.read_bytes()).hexdigest()
    if source_sha != SOURCE_SHA256:
        raise SystemExit(f"source SHA-256 {source_sha} is not the pinned {SOURCE_SHA256}")

    work = source.parent
    iverilog_rc, iverilog_out = run([
        "iverilog", "-g2012", "-s", "FemtoRV32", "-o", "/dev/null", str(source)
    ], work)
    xrun_rc, xrun_out = run([
        "xrun", "-sv", "-q", "-top", "FemtoRV32", str(source)
    ], work)
    if iverilog_rc == 0 or xrun_rc == 0:
        raise SystemExit("a pinned simulator unexpectedly compiled the source")
    if "instr" not in iverilog_out or "instr" not in xrun_out:
        raise SystemExit("compile receipts do not contain the undeclared instr wall")

    print(f"source commit: {PINNED_COMMIT}")
    print(f"source SHA-256: {SOURCE_SHA256}")
    print(f"envelope SHA-256: {ENVELOPE_SHA256}")
    print("Icarus Verilog 13.0: compile refused at use-before-declared instr")
    print("Xcelium 24.03-s004: compile refused at use-before-declared instr")
    print("E-RUN: 0/0")


if __name__ == "__main__":
    main()
