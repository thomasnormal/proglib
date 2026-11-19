#!/usr/bin/env python3
"""Differential refusal receipt for runtime initial `$error`."""
from pathlib import Path
import subprocess
import tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]

def main():
    subprocess.run(["lake", "env", "lean", str(HERE / "agree.lean")], cwd=ROOT,
                   check=True, timeout=180)
    census = subprocess.run(["python3", "harness/sv/refusal_census.py", "ordinary",
                             str(HERE / "initial_error_refuse.sv.json")], cwd=ROOT,
                            check=True, text=True, stdout=subprocess.PIPE).stdout
    if "SysCall:$error" not in census:
        raise RuntimeError(f"missing canonical-E refusal: {census}")
    print("canonical E: EXPECTED SysCall:$error refusal")
    source = HERE / "initial_error_refuse.sv"
    tb_text = """module tb; logic x; wire y; initial_error_refuse dut(.x(x), .y(y)); initial begin x=0; #1 $display(\"ROW 0 y=%b\", y); x=1'bx; #1 $display(\"ROW 1 y=%b\", y); x=1'bz; #1 $display(\"ROW 2 y=%b\", y); x=1; #1 $display(\"ROW 3 y=%b\", y); $finish; end endmodule\n"""
    expected = ["ROW 0 y=0", "ROW 1 y=x", "ROW 2 y=z", "ROW 3 y=1"]
    for sim in ("iverilog", "xrun"):
        with tempfile.TemporaryDirectory(prefix=f"sv-initial-error-{sim}-") as work:
            work = Path(work); tb = work / "tb.sv"; tb.write_text(tb_text)
            if sim == "iverilog":
                exe = work / "sim"
                subprocess.run(["iverilog", "-g2012", "-s", "tb", "-o", str(exe), str(source), str(tb)], cwd=work, check=True, timeout=180)
                proc = subprocess.run(["vvp", str(exe)], cwd=work, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True, timeout=180)
            else:
                proc = subprocess.run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "tb", str(source), str(tb)], cwd=work, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False, timeout=180)
                if proc.returncode == 0 or "ERRSEV" not in proc.stdout:
                    raise RuntimeError(f"Xcelium did not report expected $error diagnostic: {proc.stdout}")
            rows = [line for line in proc.stdout.splitlines() if line.startswith("ROW ")]
            if rows != expected: raise RuntimeError(f"{sim}: {rows} != {expected}")
        print(f"{sim}: 4 source rows MATCH")

if __name__ == "__main__":
    main()
