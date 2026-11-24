#!/usr/bin/env python3
"""Differential receipt for the memory edge-order witness."""

from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [
    ["reset", "00", "00", "00"],
    ["first", "12", "34", "00"],
    ["second", "a5", "5a", "00"],
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
  logic clk, rst;
  logic [7:0] a_in, b_in;
  wire [7:0] a_q, b_q, rd;
  {top} dut(.clk(clk), .rst(rst), .a_in(a_in), .b_in(b_in),
            .a_q(a_q), .b_q(b_q), .rd(rd));
  task show(input string tag);
    $display("ROW %s %h %h %h", tag, a_q, b_q, rd);
  endtask
  initial begin
    clk = 0; rst = 1; a_in = 0; b_in = 0;
    #1 clk = 1; #1 show("reset");
    clk = 0; rst = 0; a_in = 8'h12; b_in = 8'h34;
    #1 clk = 1; #1 show("first");
    clk = 0; a_in = 8'ha5; b_in = 8'h5a;
    #1 clk = 1; #1 show("second");
    $finish;
  end
endmodule
'''


def receipt(sim):
    source = HERE / "edge_order_memory_e.sv"
    with tempfile.TemporaryDirectory(prefix="sv-edge-memory-") as work:
        work = Path(work)
        tb = work / "tb.sv"
        tb.write_text(testbench("edge_order_memory_e"))
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
    print(f"{version}: 3 rows MATCH")


def main():
    receipt("iverilog")
    if shutil.which("xrun"):
        receipt("xrun")


if __name__ == "__main__":
    main()
