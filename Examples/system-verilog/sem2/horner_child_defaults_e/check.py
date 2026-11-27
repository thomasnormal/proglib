#!/usr/bin/env python3
"""Differential rows for hierarchical string-parameter forwarding."""
from pathlib import Path
import os
import signal
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = ["TB_RESULT rows=4 errors=0"]


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


def main():
    source = HERE / "horner_child_defaults.sv"
    tb = HERE / "horner_child_defaults_tb.sv"
    with tempfile.TemporaryDirectory(
            prefix="sv-horner-child-",
            dir=os.environ.get("SV_SCRATCH_DIR")) as work:
        work = Path(work)
        exe = work / "sim"
        run(["iverilog", "-g2012", "-s", "tb", "-o", str(exe),
             str(source), str(tb)], work)
        actual = [line.strip() for line in run(["vvp", str(exe)], work).splitlines()
                  if line.startswith("TB_RESULT")]
        if actual != EXPECTED:
            raise RuntimeError(f"Icarus Verilog 13.0: {actual} != {EXPECTED}")
        print("Icarus Verilog 13.0: 4 rows MATCH")
        if shutil.which("xrun"):
            actual = [line.strip() for line in run([
                "xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "tb",
                str(source), str(tb)], work).splitlines()
                      if line.startswith("TB_RESULT")]
            if actual != EXPECTED:
                raise RuntimeError(f"Xcelium 24.03-s004: {actual} != {EXPECTED}")
            print("Xcelium 24.03-s004: 4 rows MATCH")


if __name__ == "__main__":
    main()
