#!/usr/bin/env python3
"""Differential rows for the §6.20.2 stale-type refusal."""
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = ["ROW default=00000010 override=00000001"]


def run(command, cwd=ROOT):
    return subprocess.run(command, cwd=cwd, text=True, check=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT).stdout


run(["lake", "env", "lean", str(HERE / "agree.lean")])
with tempfile.TemporaryDirectory(prefix="sv-untyped-width-repair-") as work:
    exe = Path(work) / "sim"
    run(["iverilog", "-g2012", "-s", "untyped_width_repair_tb", "-o",
         str(exe), str(HERE / "untyped_width_repair.sv"),
         str(HERE / "untyped_width_repair_tb.sv")], work)
    rows = [line for line in run([str(exe)], work).splitlines()
            if line.startswith("ROW ")]
    if rows != EXPECTED:
        raise RuntimeError(f"Icarus rows: {rows}")
    print("Icarus Verilog 13.0: 1 row MATCH")

with tempfile.TemporaryDirectory(prefix="sv-untyped-width-repair-xcelium-") as work:
    out = run(["xrun", "-64bit", "-q", "-sv", "-timescale", "1ns/1ps",
               "-top", "untyped_width_repair_tb",
               str(HERE / "untyped_width_repair.sv"),
               str(HERE / "untyped_width_repair_tb.sv")], work)
    rows = [line for line in out.splitlines() if line.startswith("ROW ")]
    if rows != EXPECTED:
        raise RuntimeError(f"Xcelium rows: {rows}")
    print("Xcelium 24.03-s004: 1 row MATCH")
print("E: Constant:override-type refusal for stale derived localparam")
