#!/usr/bin/env python3
"""Differential receipt for the active-high asynchronous-reset boundary."""
from pathlib import Path
import shutil
import subprocess
import tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [["0", "0", "0", "x"], ["1", "0", "1", "1"],
            ["0", "1", "1", "1"], ["1", "0", "x", "x"],
            ["0", "x", "z", "z"], ["x", "0", "1", "1"],
            ["0", "z", "0", "0"], ["1", "0", "0", "0"]]
def run(cmd, cwd=ROOT, check=True):
    p = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=180)
    if check and p.returncode:
        raise RuntimeError(p.stdout)
    return p
def rows(text):
    return [line.split()[1:] for line in text.splitlines() if line.startswith("ROW ")]
def tb(top):
    return f'''`timescale 1ns/1ps
module tb;
 logic clk,rst,d; wire q;
 {top} dut(.clk(clk),.rst(rst),.d(d),.q(q));
 task show; $display("ROW %b %b %b %b",clk,rst,d,q); endtask
 initial begin
  clk=0; rst=0; d=0; #1 show;
  d=1; clk=1; #1 show;
  clk=0; rst=1; #1 show;
  rst=0; d=1'bx; clk=1; #1 show;
  clk=0; rst=1'bx; d=1'bz; #1 show;
  rst=0; clk=1'bx; d=1; #1 show;
  clk=0; rst=1'bz; d=0; #1 show;
  rst=0; clk=1; #1 show;
  $finish;
 end
endmodule
'''
def main():
    source = HERE / f"{HERE.name}.sv"
    envelope = HERE / f"{HERE.name}.sv.json"
    with tempfile.NamedTemporaryFile(suffix=".json") as f:
        run(["python3", "extractors/sv/extract.py", "--top", HERE.name,
             "-o", f.name, str(source.relative_to(ROOT))])
        if Path(f.name).read_bytes() != envelope.read_bytes():
            raise RuntimeError("stale envelope")
    with tempfile.NamedTemporaryFile("w", suffix=".lean") as f:
        f.write("import LeanModels.Sv.Ingest2\n")
        f.write(f'load_design_sv2 activeHighCheck from "{envelope}"\n')
        f.flush()
        p = run(["lake", "env", "lean", f.name], check=False)
    if p.returncode == 0 or "Clock:async-reset" not in p.stdout:
        raise RuntimeError("ordinary loader did not refuse active-high reset:\n" + p.stdout)
    print("extractor: envelope regenerates byte-identically")
    print("ordinary loader: REFUSED Clock:async-reset")
    for sim in ["iverilog"] + (["xrun"] if shutil.which("xrun") else []):
        with tempfile.TemporaryDirectory(prefix="sv-areset-high-") as work:
            tb_path = Path(work) / "tb.sv"; tb_path.write_text(tb(HERE.name))
            if sim == "iverilog":
                exe = str(Path(work) / "sim")
                run(["iverilog", "-g2012", "-s", "tb", "-o", exe,
                     str(source), str(tb_path)], work)
                output = run(["vvp", exe], work).stdout
            else:
                output = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                              "-top", "tb", str(source), str(tb_path)], work).stdout
        if rows(output) != EXPECTED:
            raise RuntimeError(f"{sim}: {rows(output)} != {EXPECTED}")
        version = run(["iverilog", "-V"] if sim == "iverilog" else ["xrun", "-version"]).stdout.splitlines()[0]
        print(f"{version}: 8 source rows MATCH simulator")
if __name__ == "__main__": main()
