#!/usr/bin/env python3
"""Differential rows for scalar storage in a generated child scope."""
from pathlib import Path
import os
import signal
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
EXPECTED = [
    "ROW 0 data=00000000 out=00000000",
    "ROW 1 data=10101100 out=10101100",
    "ROW 2 data=11110000 out=11110000",
    "ROW 3 data=xxxxxxxx out=xxxxxxxx",
    "ROW 4 data=zzzzzzzz out=zzzzzzzz",
]

def run(args, cwd):
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
    source = HERE / "generated_scalar_child_storage.sv"
    tb = HERE / "generated_scalar_child_storage_tb.sv"
    with tempfile.TemporaryDirectory(prefix="sv-generated-child-",
                                      dir=os.environ.get("SV_SCRATCH_DIR")) as work:
        work = Path(work)
        exe = work / "sim"
        run(["iverilog", "-g2012", "-s", "tb", "-o", str(exe), str(source), str(tb)], work)
        actual = [line.strip() for line in run(["vvp", str(exe)], work).splitlines()
                  if line.startswith("ROW ")]
        if actual != EXPECTED:
            raise RuntimeError(f"Icarus Verilog 13.0: {actual} != {EXPECTED}")
        print("Icarus Verilog 13.0: 5 rows MATCH")
        if shutil.which("xrun"):
            actual = [line.strip() for line in run([
                "xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "tb",
                str(source), str(tb)], work).splitlines() if line.startswith("ROW ")]
            if actual != EXPECTED:
                raise RuntimeError(f"Xcelium 24.03-s004: {actual} != {EXPECTED}")
            print("Xcelium 24.03-s004: 5 rows MATCH")

if __name__ == "__main__":
    main()
