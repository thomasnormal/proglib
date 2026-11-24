#!/usr/bin/env python3
"""Differential receipt for the simultaneous NBA acceptance witness."""

from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [
    ["0", "0", "0", "1"],
    ["1", "0", "1", "1"],
    ["0", "1", "0", "0"],
    ["1", "1", "1", "0"],
]


def run(cmd, cwd=ROOT):
    return subprocess.run(cmd, cwd=cwd, text=True, check=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                          timeout=180).stdout


def rows(text):
    return [line.split()[1:] for line in text.splitlines()
            if line.startswith("ROW ")]


def testbench(top):
    return f'''`timescale 1ns/1ps
module tb;
  logic clk_a, clk_b;
  wire a, b;
  {top} dut(.clk_a(clk_a), .clk_b(clk_b), .a(a), .b(b));
  task show;
    $display("ROW %b %b %b %b", clk_a, clk_b, a, b);
  endtask
  initial begin
    clk_a = 0; clk_b = 0;
    force dut.a = 0; force dut.b = 1;
    #1 show;
    release dut.a; release dut.b;
    clk_a = 1; #1 show;
    force dut.a = 0; force dut.b = 1;
    clk_a = 0; clk_b = 0; #1;
    release dut.a; release dut.b;
    clk_b = 1; #1 show;
    force dut.a = 0; force dut.b = 1;
    clk_a = 0; clk_b = 0; #1;
    release dut.a; release dut.b;
    clk_a = 1; clk_b = 1; #1 show;
    $finish;
  end
endmodule
'''


def receipt(sim):
    source = HERE / "simultaneous_nba.sv"
    with tempfile.TemporaryDirectory(prefix="sv-simultaneous-nba-") as work:
        work = Path(work)
        tb = work / "tb.sv"
        tb.write_text(testbench("simultaneous_nba"))
        if sim == "iverilog":
            exe = work / "sim"
            run(["iverilog", "-g2012", "-s", "tb", "-o", str(exe),
                 str(source), str(tb)], work)
            output = run(["vvp", str(exe)], work)
            version = run(["iverilog", "-V"], work).splitlines()[0]
        else:
            output = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                          "-top", "tb", str(source), str(tb)], work)
            version = run(["xrun", "-version"], work).splitlines()[0]
    got = rows(output)
    if got != EXPECTED:
        raise RuntimeError(f"{sim}: {got} != {EXPECTED}")
    print(f"{version}: 4 rows MATCH")


def main():
    receipt("iverilog")
    if shutil.which("xrun"):
        receipt("xrun")


if __name__ == "__main__":
    main()
