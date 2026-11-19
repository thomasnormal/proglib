#!/usr/bin/env python3
"""Differential refusal receipt for runtime initial `$fatal`."""
from pathlib import Path
import subprocess
import tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]

def rows(text):
    return [line.split()[1:] for line in text.splitlines() if line.startswith("CYCLE ")]

def main():
    subprocess.run(["lake", "env", "lean", str(HERE / "agree.lean")], cwd=ROOT,
                   check=True, timeout=180)
    census = subprocess.run(["python3", "harness/sv/refusal_census.py", "ordinary",
                             str(HERE / "initial_const_fatal.sv.json")], cwd=ROOT,
                            check=True, text=True, stdout=subprocess.PIPE).stdout
    if "SysCall:$fatal" not in census:
        raise RuntimeError(f"missing canonical-E refusal: {census}")
    print("canonical E: EXPECTED SysCall:$fatal refusal")
    source = HERE / "initial_const_fatal.sv"
    expected = [["0", "q=0"], ["1", "q=1"], ["2", "q=x"], ["3", "q=z"]]
    tb_text = """module tb; logic clk=0,d; wire q; initial_const_fatal #(.N(1)) dut(clk,d,q); integer i=0; task s(input logic v); begin d=v;#1 clk=1;#1 $display(\"CYCLE %0d q=%b\",i,q);clk=0;#1;i=i+1;end endtask initial begin s(0);s(1);s(1'bx);s(1'bz);$finish;end endmodule\n"""
    for sim in ("iverilog", "xrun"):
        with tempfile.TemporaryDirectory(prefix=f"sv-initial-fatal-{sim}-") as work:
            work = Path(work)
            tb = work / "tb.sv"
            tb.write_text(tb_text)
            if sim == "iverilog":
                exe = work / "sim"
                subprocess.run(["iverilog", "-g2012", "-s", "tb", "-o", str(exe), str(source), str(tb)],
                               cwd=work, check=True, timeout=180)
                out = subprocess.run(["vvp", str(exe)], cwd=work, check=True,
                                     text=True, stdout=subprocess.PIPE).stdout
            else:
                out = subprocess.run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "tb",
                                      str(source), str(tb)], cwd=work, check=True,
                                     text=True, stdout=subprocess.PIPE,
                                     stderr=subprocess.STDOUT, timeout=180).stdout
            if rows(out) != expected:
                raise RuntimeError(f"{sim}: {rows(out)} != {expected}")
            print(f"Xcelium 24.03-s004: 4 rows MATCH for N=1" if sim == "xrun" else
                  "Icarus Verilog 13.0: 4 rows MATCH for N=1")

if __name__ == "__main__":
    main()
