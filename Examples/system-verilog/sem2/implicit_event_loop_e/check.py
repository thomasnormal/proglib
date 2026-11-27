#!/usr/bin/env python3
"""Differential rows for a plain always @* procedural loop."""
from pathlib import Path
import os
import signal
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [
    "ROW 0 a=0000 y=0000", "ROW 1 a=0001 y=0011",
    "ROW 2 a=1010 y=0000", "ROW 3 a=xxxx y=0000",
    "ROW 4 a=zzzz y=0000",
]


def run(args, cwd=ROOT):
    proc = subprocess.Popen(args, cwd=cwd, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, start_new_session=True)
    try:
        out, err = proc.communicate(timeout=240)
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        raise RuntimeError(f"{args[0]} timed out")
    if proc.returncode:
        raise RuntimeError(f"{args[0]} exited {proc.returncode}: {err}")
    return out


def rows(out):
    return [line.strip() for line in out.splitlines() if line.startswith("ROW ")]


def main():
    source = HERE / "implicit_event_loop.sv"
    tb = HERE / "implicit_event_loop_tb.sv"
    with tempfile.TemporaryDirectory(prefix="sv-implicit-loop-") as work:
        work = Path(work)
        exe = work / "sim"
        run(["iverilog", "-g2012", "-s", "tb", "-o", str(exe),
             str(source), str(tb)], work)
        actual = rows(run(["vvp", str(exe)], work))
        if actual != EXPECTED:
            raise RuntimeError(f"Icarus Verilog 13.0: {actual} != {EXPECTED}")
        print("Icarus Verilog 13.0: 5 rows MATCH")
        if shutil.which("xrun"):
            actual = rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                               "-top", "tb", str(source), str(tb)], work))
            if actual != EXPECTED:
                raise RuntimeError(f"Xcelium 26.09-s001: {actual} != {EXPECTED}")
            print("Xcelium 26.09-s001: 5 rows MATCH")


if __name__ == "__main__":
    main()
