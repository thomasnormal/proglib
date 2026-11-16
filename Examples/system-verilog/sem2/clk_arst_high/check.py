#!/usr/bin/env python3
"""Differential receipt for active-high asynchronous reset in canonical E."""
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [
    ["0", "0", "0", "0001", "x" * 4],
    ["0", "1", "0", "0001", "0000"],
    ["0", "0", "1", "0110", "0000"],
    ["1", "0", "1", "0110", "0110"],
    ["1", "x", "1", "1111", "1111"],
    ["1", "0", "1", "1111", "1111"],
    ["1", "z", "1", "0010", "0010"],
    ["1", "0", "1", "0010", "0010"],
    ["1", "1", "1", "0010", "0000"],
    ["0", "1", "1", "0010", "0000"],
    ["0", "0", "1", "0010", "0000"],
    ["x", "0", "1", "0011", "0011"],
    ["1", "0", "1", "0100", "0100"],
    ["0", "0", "1", "0100", "0100"],
    ["z", "0", "1", "0101", "0101"],
    ["1", "0", "1", "0110", "0110"],
    ["x", "0", "1", "0111", "0110"],
    ["z", "0", "1", "0111", "0110"],
    ["1", "0", "1", "0111", "0111"],
]


def run(cmd, cwd=ROOT):
    p = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=180)
    if p.returncode:
        raise RuntimeError(f"{cmd[0]} exited {p.returncode}:\n{p.stdout}")
    return p.stdout


def rows(text):
    return [line.split()[1:] for line in text.splitlines()
            if line.startswith("ROW ")]


def testbench():
    return r'''`timescale 1ns/1ps
module tb;
  logic clk, rst, en; logic [3:0] d; wire [3:0] q;
  clk_arst_high #(.N(4)) dut(.clk(clk), .rst(rst), .en(en), .d(d), .q(q));
  task show; $display("ROW %b %b %b %b %b", clk, rst, en, d, q); endtask
  initial begin
    clk=0; rst=0; en=0; d=4'b0001; #1 show;
    rst=1; #1 show;
    rst=0; en=1; d=4'b0110; #1 show;
    clk=1; #1 show;
    rst=1'bx; d=4'b1111; #1 show;
    rst=1'b0; #1 show;
    rst=1'bz; d=4'b0010; #1 show;
    rst=1'b0; #1 show;
    rst=1'b1; #1 show;
    clk=0; #1 show;
    rst=0; #1 show;
    d=4'b0011; clk=1'bx; #1 show;
    d=4'b0100; clk=1; #1 show;
    clk=0; #1 show;
    d=4'b0101; clk=1'bz; #1 show;
    d=4'b0110; clk=1; #1 show;
    clk=1'bx; d=4'b0111; #1 show;
    clk=1'bz; #1 show;
    clk=1; #1 show;
    $finish;
  end
endmodule
'''


def main():
    source = HERE / "clk_arst_high.sv"
    envelope = HERE / "clk_arst_high.sv.json"
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    with tempfile.TemporaryDirectory(prefix="sv-arst-high-") as work:
        tb = Path(work) / "tb.sv"
        tb.write_text(testbench())
        exe = str(Path(work) / "sim")
        run(["iverilog", "-g2012", "-s", "tb", "-o", exe,
             str(source), str(tb)], work)
        actual = rows(run(["vvp", exe], work))
    if actual != EXPECTED:
        raise RuntimeError(f"Icarus: {actual} != {EXPECTED}")
    print("canonical E + ordinary loader: active-high reset admitted")
    print("Icarus Verilog 13.0: 19 source rows MATCH, including x/z reset and clock edges")

    if shutil.which("xrun"):
        with tempfile.TemporaryDirectory(prefix="sv-arst-high-xrun-") as work:
            tb = Path(work) / "tb.sv"
            tb.write_text(testbench())
            actual = rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                               "-top", "tb", str(source), str(tb)], work))
        if actual != EXPECTED:
            raise RuntimeError(f"Xcelium: {actual} != {EXPECTED}")
        print("Xcelium 24.03-s004: 19 source rows MATCH, including x/z reset and clock edges")


if __name__ == "__main__":
    main()
