#!/usr/bin/env python3
"""Differential receipt for the mixed negedge clock/reset loader boundary."""
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [
    ["1", "x", "0", "x"], ["1", "0", "0", "0"],
    ["1", "1", "0", "0"], ["0", "1", "1", "1"],
    ["1", "1", "0", "1"], ["0", "1", "0", "0"],
    ["0", "0", "0", "0"], ["1", "1", "1", "0"],
]
TB = r'''`timescale 1ns/1ps
module tb;
  logic clk=1'b1, rst_n=1'bx, d=1'b0; wire q;
  loader_refuse_negedge_reset dut(.clk(clk), .rst_n(rst_n), .d(d), .q(q));
  task show; $display("ROW %b %b %b %b", clk, rst_n, d, q); endtask
  initial begin
    #1 show; rst_n=0; #1 show; rst_n=1; #1 show;
    d=1; clk=0; #1 show; d=0; clk=1; #1 show;
    clk=0; #1 show; rst_n=0; #1 show;
    rst_n=1; d=1; clk=1; #1 show; $finish;
  end
endmodule
'''

def run(args, cwd):
    proc = subprocess.run(args, cwd=cwd, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                          timeout=180)
    if proc.returncode:
        raise RuntimeError(f"{args[0]} exited {proc.returncode}:\n{proc.stdout}")
    return proc.stdout

def rows(output):
    return [line.split()[1:] for line in output.splitlines()
            if line.startswith("ROW ")]

def main():
    with tempfile.TemporaryDirectory(prefix="sv-negedge-reset-") as work:
        tb = Path(work) / "tb.sv"
        tb.write_text(TB)
        source = HERE / "loader_refuse_negedge_reset.sv"
        for simulator in ("iverilog", "xrun"):
            if simulator == "iverilog":
                exe = str(Path(work) / "sim")
                run(["iverilog", "-g2012", "-s", "tb", "-o", exe,
                     str(source), str(tb)], work)
                actual = rows(run(["vvp", exe], work))
            else:
                actual = rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                                   "-top", "tb", str(source), str(tb)], work))
            if actual != EXPECTED:
                raise RuntimeError(f"{simulator}: {actual} != {EXPECTED}")
            print(f"{simulator}: 8 rows MATCH")
    run(["lake", "env", "lean", str(HERE / "agree.lean")], ROOT)
    print("ordinary loader: REFUSED TimedStatement:EventListControl")

if __name__ == "__main__":
    main()
