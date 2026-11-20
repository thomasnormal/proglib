#!/usr/bin/env python3
"""Receipt for the package assignment-pattern storage wall."""
from pathlib import Path
import subprocess
import tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]

def main():
    subprocess.run(["lake", "env", "lean", str(HERE / "agree.lean")], cwd=ROOT,
                   check=True, timeout=180)
    census = subprocess.run(["python3", "harness/sv/refusal_census.py", "ordinary",
                             str(HERE / "assignment_pattern_storage_refuse.sv.json")],
                            cwd=ROOT, check=True, text=True,
                            stdout=subprocess.PIPE).stdout
    if "aggregate default shape is unsupported" not in census:
        raise RuntimeError(f"missing assignment-pattern refusal: {census}")
    print("canonical E: EXPECTED aggregate assignment-pattern default refusal")
    source = HERE / "assignment_pattern_storage_refuse.sv"
    tb_text = '''module tb; logic x; wire y; assignment_pattern_storage_refuse dut(.x(x), .y(y)); initial begin x=0; #1 $display("ROW 0 y=%b", y); x=1'bx; #1 $display("ROW 1 y=%b", y); x=1'bz; #1 $display("ROW 2 y=%b", y); x=1; #1 $display("ROW 3 y=%b", y); $finish; end endmodule\n'''
    expected = ["ROW 0 y=0", "ROW 1 y=x", "ROW 2 y=x", "ROW 3 y=1"]
    for sim in ("iverilog", "xrun"):
        with tempfile.TemporaryDirectory(prefix=f"sv-assignment-pattern-{sim}-", dir="/scratch/thomas-ahle/gate/ls-sv/tmp") as work:
            work = Path(work); tb = work / "tb.sv"; tb.write_text(tb_text)
            if sim == "iverilog":
                exe = work / "sim"
                proc = subprocess.run(["iverilog", "-g2012", "-s", "tb", "-o", str(exe), str(source), str(tb)], cwd=work, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=False, timeout=180)
                if proc.returncode == 0 or "syntax error" not in proc.stdout:
                    raise RuntimeError(f"iverilog unexpectedly accepted the faithful source: {proc.stdout}")
                print("iverilog: EXPECTED source syntax refusal")
                continue
            else:
                proc = subprocess.run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "tb", str(source), str(tb)], cwd=work, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True, timeout=180)
            rows = [line for line in proc.stdout.splitlines() if line.startswith("ROW ")]
            if rows != expected:
                raise RuntimeError(f"{sim}: {rows} != {expected}\n{proc.stdout}")
        print(f"{sim}: 4 source rows MATCH")

if __name__ == "__main__":
    main()
