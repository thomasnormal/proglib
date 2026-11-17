#!/usr/bin/env python3
"""Receipt for the internal-reset refusal and its simulator edge trace."""
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [
    ["0", "1", "1", "x"], ["1", "1", "1", "0"],
    ["0", "0", "0", "0"], ["1", "0", "0", "0"],
    ["0", "x", "1", "0"], ["1", "x", "1", "1"],
    ["0", "z", "0", "1"], ["1", "z", "0", "0"],
    ["0", "0", "x", "0"], ["1", "0", "x", "x"],
]
TB = r'''`timescale 1ns/1ps
module tb;
 logic clk,rst,d; wire q;
 clk_rst_int dut(.clk(clk),.rst(rst),.d(d),.q(q));
 task show; $display("ROW %b %b %b %b",clk,rst,d,q); endtask
 initial begin
  clk=0; rst=1; d=1; #1 show; clk=1; #1 show;
  clk=0; rst=0; d=0; #1 show; clk=1; #1 show;
  clk=0; rst=1'bx; d=1; #1 show; clk=1; #1 show;
  clk=0; rst=1'bz; d=0; #1 show; clk=1; #1 show;
  clk=0; rst=0; d=1'bx; #1 show; clk=1; #1 show; $finish;
 end
endmodule
'''


def run(cmd, cwd=ROOT):
    p = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=180)
    if p.returncode:
        raise RuntimeError(p.stdout)
    return p.stdout


def rows(s):
    return [x.split()[1:] for x in s.splitlines() if x.startswith("ROW ")]


def main():
    with tempfile.TemporaryDirectory(prefix="sv-internal-reset-") as work:
        tb = Path(work) / "tb.sv"; tb.write_text(TB)
        for sim in ("iverilog", "xrun"):
            if sim == "iverilog":
                exe = str(Path(work) / "sim")
                run(["iverilog", "-g2012", "-s", "tb", "-o", exe,
                     str(HERE / "clk_rst_int.sv"), str(tb)], work)
                actual = rows(run(["vvp", exe], work))
            else:
                actual = rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                                   "-top", "tb", str(HERE / "clk_rst_int.sv"), str(tb)], work))
            if actual != EXPECTED:
                raise RuntimeError(f"{sim}: {actual} != {EXPECTED}")
            print(f"{sim}: 10 x/z rows MATCH")
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    print("ordinary loader: REFUSED Clock:reset; canonical E: named event-source boundary")


if __name__ == "__main__":
    main()
