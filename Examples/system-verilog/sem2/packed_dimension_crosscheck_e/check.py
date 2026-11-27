#!/usr/bin/env python3
from pathlib import Path
import os, signal, shutil, subprocess, tempfile
HERE = Path(__file__).resolve().parent
EXPECTED = ["TB_RESULT rows=1 errors=0"]
def run(args, cwd):
    p = subprocess.Popen(args, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
    try: out, err = p.communicate(timeout=240)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL); raise RuntimeError(f"{args[0]} timed out")
    if p.returncode: raise RuntimeError(f"{args[0]} exited {p.returncode}: {err}")
    return out
def main():
    with tempfile.TemporaryDirectory(prefix="sv-packed-crosscheck-", dir=os.environ.get("SV_SCRATCH_DIR")) as w:
        w = Path(w); exe = w / "sim"; src = HERE / "packed_dimension_crosscheck.sv"; tb = HERE / "packed_dimension_crosscheck_tb.sv"
        run(["iverilog", "-g2012", "-s", "tb", "-o", str(exe), str(src), str(tb)], w)
        rows = [x.strip() for x in run(["vvp", str(exe)], w).splitlines() if x.startswith("TB_RESULT")]
        if rows != EXPECTED: raise RuntimeError(f"Icarus Verilog 13.0: {rows} != {EXPECTED}")
        print("Icarus Verilog 13.0: 1 row MATCH")
        if shutil.which("xrun"):
            rows = [x.strip() for x in run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "tb", str(src), str(tb)], w).splitlines() if x.startswith("TB_RESULT")]
            if rows != EXPECTED: raise RuntimeError(f"Xcelium 24.03-s004: {rows} != {EXPECTED}")
            print("Xcelium 24.03-s004: 1 row MATCH")
if __name__ == "__main__": main()
