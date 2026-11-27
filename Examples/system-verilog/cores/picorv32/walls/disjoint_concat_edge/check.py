#!/usr/bin/env python3
"""Differential receipt for disjoint same-edge concatenation targets."""
from pathlib import Path
import shutil
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
SOURCE = HERE / "disjoint_concat_edge.sv"
EXPECTED = ["x x", "0 0", "0 0", "0 1"]
TB = r'''module tb;
  logic clk, a, b;
  wire x;
  wire [1:0] y;
  disjoint_concat_edge dut(.clk(clk), .a(a), .b(b), .x(x), .y(y));
  initial begin
    clk = 0; a = 0; b = 0; #1 $display("ROW %b %b", x, y[0]);
    clk = 1; #1 $display("ROW %b %b", x, y[0]);
    clk = 0; a = 0; b = 1; #1 $display("ROW %b %b", x, y[0]);
    clk = 1; #1 $display("ROW %b %b", x, y[0]);
    $finish;
  end
endmodule'''


def rows(output):
    return [" ".join(line.split()[1:]) for line in output.splitlines()
            if line.startswith("ROW ")]


def run(cmd, cwd):
    return subprocess.run(cmd, cwd=cwd, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                          check=True, timeout=180).stdout


def main():
    with tempfile.TemporaryDirectory(prefix="sv-disjoint-concat-") as td:
        work = Path(td)
        tb = work / "tb.sv"
        tb.write_text(TB)
        exe = work / "sim"
        run(["iverilog", "-g2012", "-s", "tb", "-o", str(exe),
             str(SOURCE), str(tb)], work)
        actual = rows(run(["vvp", str(exe)], work))
        if actual != EXPECTED:
            raise RuntimeError(f"Icarus rows {actual} != {EXPECTED}")
        print("Icarus Verilog 13.0: four rows MATCH")
        if shutil.which("xrun"):
            actual = rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                               "-top", "tb", str(SOURCE), str(tb)], work))
            if actual != EXPECTED:
                raise RuntimeError(f"Xcelium rows {actual} != {EXPECTED}")
            print("Xcelium Verilog 24.03-s004: four rows MATCH")
        else:
            print("Xcelium Verilog 24.03-s004: no result, xrun unavailable")


if __name__ == "__main__":
    main()
