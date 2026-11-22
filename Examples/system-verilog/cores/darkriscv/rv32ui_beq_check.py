#!/usr/bin/env python3
"""Run one pinned riscv-tests rv32ui image through both simulators and E."""

from __future__ import annotations

import hashlib
import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

import battery_check as canonical_battery
from battery_check import FIELDS, expected_rows, run_lean


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCE = HERE / "rtl" / "darkriscv.v"
TESTBENCH = HERE / "rv32ui_beq_tb.sv"
IMAGE = HERE / "rv32ui_beq.hex"
TRANSCRIPT = HERE / "rv32ui_beq_simulator_transcript.txt"
SOURCE_SHA256 = "46d57b15cc42c0458e02500a2a30371cd4e7979970c27afd9d47c40d1fa8c1a0"
TESTBENCH_SHA256 = "089da9e98709486372a1261d465e7e8b7579255b1ae591e503356053a7641293"
IMAGE_SHA256 = "d891ad9b452fdd4f7c6964f1cf86ba51cfbedea258a524b4fa0cc1e07677cc18"
TRANSCRIPT_SHA256 = "24e77902b5ea86b03ae5cb48c8e443d75b68809d34e27d13e107ed87926b99e5"
EXPECTED_CYCLES = 300


def run(command: list[str], cwd: Path) -> str:
    result = subprocess.run(
        command, cwd=cwd, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, check=False, timeout=900,
    )
    if result.returncode:
        raise RuntimeError("command failed (%d): %s\n%s" %
                           (result.returncode, " ".join(command), result.stdout))
    return result.stdout


def parse_rows(output: str) -> list[dict[str, str]]:
    rows = [dict(re.findall(r"(\w+)=([^ ]+)", line))
            for line in output.splitlines() if line.startswith("ROW ")]
    if len(rows) != EXPECTED_CYCLES:
        raise RuntimeError(f"expected {EXPECTED_CYCLES} rows, got {len(rows)}")
    for row in rows:
        required = {name for name, _, _ in FIELDS} | {"cycle", "instr_ack"}
        if set(row) != required:
            raise RuntimeError(f"simulator row fields changed: {sorted(row)}")
    return rows


def raw_rows(rows: list[dict[str, str]]) -> list[str]:
    return ["ROW " + " ".join(f"{name}={value}" for name, value in row.items())
            for row in rows]


def simulator_rows() -> tuple[list[dict[str, str]], list[dict[str, str]]]:
    with tempfile.TemporaryDirectory(prefix="darkriscv-rv32ui-beq-",
                                      dir=os.environ.get("TMPDIR")) as work:
        directory = Path(work)
        sim_work = directory / "sim"
        sim_work.mkdir()
        (directory / "rtl").symlink_to(SOURCE.parent, target_is_directory=True)
        (sim_work / IMAGE.name).symlink_to(IMAGE)
        executable = directory / "darkriscv-rv32ui-beq"
        common = ["-g2012", "-DSIMULATION", "-I", str(SOURCE.parent),
                  "-o", str(executable), str(TESTBENCH), str(SOURCE)]
        run(["iverilog", *common], sim_work)
        icarus = parse_rows(run(["vvp", str(executable)], sim_work))
        xcelium = parse_rows(run([
            "xrun", "-sv", "-q", "-define", "SIMULATION", "-I../rtl",
            "-top", "darkriscv_rv32ui_beq_tb", str(TESTBENCH), str(SOURCE),
        ], sim_work))
    return icarus, xcelium


def main() -> int:
    canonical_battery.EXPECTED_CYCLES = EXPECTED_CYCLES
    if shutil.which("iverilog") is None or shutil.which("xrun") is None:
        raise SystemExit("Icarus Verilog 13.0 and Xcelium 24.03-s004 are required")
    for path, digest in ((SOURCE, SOURCE_SHA256),
                         (TESTBENCH, TESTBENCH_SHA256),
                         (IMAGE, IMAGE_SHA256),
                         (TRANSCRIPT, TRANSCRIPT_SHA256)):
        if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise SystemExit(f"pinned hash mismatch: {path}")
    icarus, xcelium = simulator_rows()
    if icarus != xcelium:
        raise SystemExit("Icarus and Xcelium disagree on rv32ui/beq rows")
    transcript = parse_rows(TRANSCRIPT.read_text())
    if transcript != icarus:
        raise SystemExit("checked-in rv32ui/beq transcript differs from simulators")
    if not any(row["instr_ack"] == "0" for row in icarus):
        raise SystemExit("rv32ui/beq image did not exercise an instruction stall")
    lean_ok, corrupted_ok, first_mismatch = run_lean(expected_rows(raw_rows(icarus)))
    if not lean_ok:
        raise SystemExit("canonical E differs at " + first_mismatch)
    if corrupted_ok:
        raise SystemExit("negative control accepted a corrupted row")
    print("riscv-tests commit: 3df703cd52d5f0d8224e3c50bf03c6cb70efff98")
    print("riscv-tests program: rv32ui/beq.S")
    print("Icarus Verilog 13.0 (s20250103-64-gdad78d525)")
    print("Xcelium 24.03-s004")
    print(f"three-way rv32ui/beq rows: {len(icarus)}/{EXPECTED_CYCLES} agree bit-for-bit")
    print(f"simulator-transcript-sha256: {TRANSCRIPT_SHA256}")
    print("negative control: corrupted cycle row rejected by the Lean comparator")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
