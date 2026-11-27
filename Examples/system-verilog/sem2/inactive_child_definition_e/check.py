#!/usr/bin/env python3
"""Differential rows for an undefined child in an inactive generate arm."""
from pathlib import Path
import os
import signal
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = ["ROW 0 a=0 y=0", "ROW 1 a=1 y=1", "ROW 2 a=x y=x", "ROW 3 a=z y=z"]


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
    source = HERE / "inactive_child_definition.sv"
    tb = HERE / "inactive_child_definition_tb.sv"
    with tempfile.TemporaryDirectory(prefix="sv-inactive-child-") as work:
        work = Path(work)
        exe = work / "sim"
        run(["iverilog", "-g2012", "-s", "tb", "-o", str(exe),
             str(source), str(tb)], work)
        actual = rows(run(["vvp", str(exe)], work))
        if actual != EXPECTED:
            raise RuntimeError(f"Icarus Verilog 13.0: {actual} != {EXPECTED}")
        print("Icarus Verilog 13.0: 4 rows MATCH")
        if shutil.which("xrun"):
            actual = rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                               "-top", "tb", str(source), str(tb)], work))
            if actual != EXPECTED:
                raise RuntimeError(f"Xcelium 26.09-s001: {actual} != {EXPECTED}")
            print("Xcelium 26.09-s001: 4 rows MATCH")


if __name__ == "__main__":
    main()
