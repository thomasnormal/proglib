#!/usr/bin/env python3
"""Differential receipt for a clocked async-reset admission guard."""
from pathlib import Path
import shutil
import subprocess
import tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [["0", "0", "0", "0"], ["1", "0", "1", "0"],
            ["0", "1", "1", "0"], ["1", "1", "x", "x"],
            ["0", "x", "z", "z"], ["x", "0", "1", "0"],
            ["0", "z", "0", "0"], ["1", "0", "0", "0"]]
TB = '''module tb; logic clk,rst_n,d; wire q;
clocked_reset_guard_e dut(.clk(clk),.rst_n(rst_n),.d(d),.q(q));
task show; $display("ROW %b %b %b %b",clk,rst_n,d,q); endtask
initial begin
 clk=0; rst_n=0; d=0; #1 show;
 clk=1; d=1; #1 show;
 clk=0; rst_n=1; #1 show;
 clk=1; rst_n=1; d=1'bx; #1 show;
 clk=0; rst_n=1'bx; d=1'bz; #1 show;
 clk=1'bx; rst_n=0; d=1; #1 show;
 clk=0; rst_n=1'bz; d=0; #1 show;
 clk=1; rst_n=0; #1 show; $finish; end endmodule'''
def run(cmd, cwd=ROOT):
    p = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=180)
    if p.returncode:
        raise RuntimeError(p.stdout)
    return p.stdout
def rows(text):
    return [line.split()[1:] for line in text.splitlines() if line.startswith("ROW ")]
def main():
    source = HERE / "clocked_reset_guard_e.sv"
    envelope = HERE / "clocked_reset_guard_e.sv.json"
    with tempfile.NamedTemporaryFile(suffix=".json") as f:
        run(["python3", "extractors/sv/extract.py", "--top", HERE.name,
             "-o", f.name, str(source.relative_to(ROOT))])
        if Path(f.name).read_bytes() != envelope.read_bytes():
            raise RuntimeError("stale envelope")
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    for sim in ["iverilog"] + (["xrun"] if shutil.which("xrun") else []):
        with tempfile.TemporaryDirectory(prefix="sv-clocked-reset-") as work:
            tb = Path(work) / "tb.sv"; tb.write_text(TB)
            if sim == "iverilog":
                exe = str(Path(work) / "sim")
                run(["iverilog", "-g2012", "-s", "tb", "-o", exe,
                     str(source), str(tb)], work)
                out = run(["vvp", exe], work)
            else:
                out = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                           "-top", "tb", str(source), str(tb)], work)
        if rows(out) != EXPECTED:
            raise RuntimeError(f"{sim}: {rows(out)} != {EXPECTED}")
        version = run(["iverilog", "-V"] if sim == "iverilog" else ["xrun", "-version"]).splitlines()[0]
        print(f"{version}: 8 x/z rows MATCH")
    print("canonical E: clocked async-reset admission MATCH")
if __name__ == "__main__":
    main()
