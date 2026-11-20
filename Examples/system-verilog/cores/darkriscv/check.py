#!/usr/bin/env python3
"""Run the pinned DarkRISCV simulator witness with both approved simulators."""

from __future__ import annotations

import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


PINNED_COMMIT = "bb6b483cc61a2886a0602c7e62b14f5995ddfbb9"
SOURCE_SHA256 = "46d57b15cc42c0458e02500a2a30371cd4e7979970c27afd9d47c40d1fa8c1a0"
EXPECTED_ROWS = 1000


def run(command: list[str], cwd: Path) -> str:
    result = subprocess.run(
        command,
        cwd=cwd,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    return result.stdout


def rows(output: str) -> list[str]:
    return [line for line in output.splitlines() if line.startswith("ROW ")]


def main() -> None:
    root_text = os.environ.get("DARKRISCV_ROOT")
    if not root_text:
        raise SystemExit("set DARKRISCV_ROOT to the pinned DarkRISCV checkout")
    root = Path(root_text).resolve()
    source = root / "rtl" / "darkriscv.v"
    if not source.is_file():
        raise SystemExit(f"missing pinned source: {source}")
    commit = run(["git", "rev-parse", "HEAD"], root).strip()
    if commit != PINNED_COMMIT:
        raise SystemExit(f"source commit {commit} is not the pinned {PINNED_COMMIT}")
    source_sha = hashlib.sha256(source.read_bytes()).hexdigest()
    if source_sha != SOURCE_SHA256:
        raise SystemExit(f"source SHA-256 {source_sha} is not the pinned {SOURCE_SHA256}")

    repo = Path(__file__).resolve().parents[4]
    testbench = repo / "Examples/system-verilog/cores/darkriscv/nop_tb.sv"
    sim_dir = root / "sim"
    with tempfile.TemporaryDirectory(prefix="darkriscv-receipt-") as temporary:
        work = Path(temporary)
        iverilog = work / "darkriscv-iverilog"
        run([
            "iverilog", "-g2012", "-I", str(root / "rtl"), "-o", str(iverilog),
            str(testbench), str(source),
        ], sim_dir)
        icarus_rows = rows(run(["vvp", str(iverilog)], sim_dir))
        print("Icarus Verilog 13.0 (s20250103-64-gdad78d525)")

        if shutil.which("xrun") is None:
            raise SystemExit("Xcelium xrun is required for this receipt")
        xcelium_rows = rows(run([
            "xrun", "-sv", "-q", "-I../rtl", "-top",
            "darkriscv_nop_tb", str(testbench), str(source),
        ], sim_dir))
        print("Xcelium 24.03-s004")

    if len(icarus_rows) != EXPECTED_ROWS or len(xcelium_rows) != EXPECTED_ROWS:
        raise SystemExit(
            f"expected {EXPECTED_ROWS} rows, got Icarus={len(icarus_rows)} "
            f"Xcelium={len(xcelium_rows)}"
        )
    if icarus_rows != xcelium_rows:
        raise SystemExit("the pinned simulators disagree on the 1000-cycle witness")
    digest = hashlib.sha256(("\n".join(icarus_rows) + "\n").encode()).hexdigest()
    print(f"rows: {EXPECTED_ROWS}/{EXPECTED_ROWS} agree")
    print(f"normalized-row-sha256: {digest}")


if __name__ == "__main__":
    main()
