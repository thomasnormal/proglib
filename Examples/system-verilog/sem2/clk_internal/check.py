#!/usr/bin/env python3
"""Receipt for the internal-clock refusal and its simulator edge trace."""
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [
    ["0", "1", "x"], ["0", "0", "x"], ["1", "1", "1"],
    ["0", "0", "1"], ["1", "1", "1"], ["x", "0", "1"],
    ["z", "1", "1"], ["0", "0", "1"], ["1", "x", "x"],
    ["0", "1", "x"],
]
TB = r'''`timescale 1ns/1ps
module tb;
 logic sel,d; wire q;
 clk_internal dut(.sel(sel),.d(d),.q(q));
 task show; $display("ROW %b %b %b",sel,d,q); endtask
 initial begin
  sel=0; d=1; #1 show; sel=0; d=0; #1 show;
  sel=1; d=1; #1 show; sel=0; d=0; #1 show;
  sel=1; d=1; #1 show; sel=1'bx; d=0; #1 show;
  sel=1'bz; d=1; #1 show; sel=0; d=0; #1 show;
  sel=1; d=1'bx; #1 show; sel=0; d=1; #1 show; $finish;
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
    with tempfile.TemporaryDirectory(prefix="sv-internal-clock-") as work:
        tb = Path(work) / "tb.sv"; tb.write_text(TB)
        for sim in ("iverilog", "xrun"):
            if sim == "iverilog":
                exe = str(Path(work) / "sim")
                run(["iverilog", "-g2012", "-s", "tb", "-o", exe,
                     str(HERE / "clk_internal.sv"), str(tb)], work)
                actual = rows(run(["vvp", exe], work))
            else:
                actual = rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                                   "-top", "tb", str(HERE / "clk_internal.sv"), str(tb)], work))
            if actual != EXPECTED:
                raise RuntimeError(f"{sim}: {actual} != {EXPECTED}")
            print(f"{sim}: 10 x/z rows MATCH")
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    print("ordinary loader: REFUSED Clock:source; canonical E census: REFUSED Clock:source")


if __name__ == "__main__":
    main()
