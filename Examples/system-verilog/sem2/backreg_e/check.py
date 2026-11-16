#!/usr/bin/env python3
"""Differential receipt for the topological continuous-assignment boundary."""

from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [
    ["0101", "xxxx"], ["0101", "0101"], ["0101", "0101"],
    ["1001", "0101"], ["1001", "1001"], ["1001", "1001"],
    ["xxxx", "1001"], ["zzzz", "1001"],
]


def run(cmd, cwd=ROOT):
    p = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=180)
    if p.returncode:
        raise RuntimeError(p.stdout)
    return p.stdout


def rows(text):
    return [line.split()[2:] for line in text.splitlines()
            if line.startswith("ROW ")]


def tb(top):
    return f'''`timescale 1ns/1ps
module tb;
  logic clk; logic [3:0] x; wire [3:0] a;
  {top} dut(.clk(clk), .x(x), .a(a));
  task row(input logic [3:0] xv, input logic cv);
    begin x=xv; clk=cv; #1 $display("ROW %b %b %b", clk, x, a); end
  endtask
  initial begin
    row(4'b0101, 1'b0); row(4'b0101, 1'b1);
    row(4'b0101, 1'b0); row(4'b1001, 1'b0);
    row(4'b1001, 1'b1); row(4'b1001, 1'b0);
    row(4'bxxxx, 1'b0); row(4'bzzzz, 1'b0);
    $finish;
  end
endmodule
'''


def main():
    top = HERE.name
    source = HERE / f"{top}.sv"
    envelope = HERE / f"{top}.sv.json"
    with tempfile.NamedTemporaryFile(suffix=".json") as f:
        run(["python3", "extractors/sv/extract.py", "--top", top, "-o",
             f.name, str(source.relative_to(ROOT))])
        if Path(f.name).read_bytes() != envelope.read_bytes():
            raise RuntimeError("stale envelope")
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    print("extractor: envelope regenerates byte-identically")
    print("E: REFUSED 10.3 topological continuous-assignment boundary")
    simulators = ["iverilog"] + (["xrun"] if shutil.which("xrun") else [])
    for sim in simulators:
        with tempfile.TemporaryDirectory(prefix="sv-backreg-") as work:
            tb_path = Path(work) / "tb.sv"
            tb_path.write_text(tb(top))
            if sim == "iverilog":
                exe = str(Path(work) / "sim")
                run(["iverilog", "-g2012", "-s", "tb", "-o", exe,
                     str(source), str(tb_path)], work)
                output = run(["vvp", exe], work)
            else:
                output = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                              "-top", "tb", str(source), str(tb_path)], work)
        actual = rows(output)
        if actual != EXPECTED:
            raise RuntimeError(f"{sim}: {actual} != {EXPECTED}")
        version = run(["iverilog", "-V"] if sim == "iverilog"
                      else ["xrun", "-version"]).splitlines()[0]
        print(f"{version}: 8 source rows MATCH simulator")


if __name__ == "__main__":
    main()
