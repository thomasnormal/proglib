#!/usr/bin/env python3
"""Receipt for parser-native parameter-bound procedural-loop retention."""
from pathlib import Path
import shutil
import subprocess
import tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [["0000", "xxxx"], ["0001", "xxxx"], ["0010", "xxxx"], ["0010", "xxxx"],
            ["0011", "xxxx"], ["0011", "0001"], ["xxxx", "0001"], ["zzzz", "0010"]]
TB = '''module tb; logic clk; logic [3:0] d; wire [3:0] q;
clocked_param_loop_e dut(.clk(clk),.d(d),.q(q));
task show; $display("ROW %b %b",d,q); endtask
initial begin clk=0; d=0; #1 show; d=1; clk=1; #1 show; clk=0; d=2; #1 show;
clk=1; #1 show; clk=0; d=3; #1 show; clk=1; #1 show; d=4'bx; clk=0; #1 show;
d=4'bz; clk=1; #1 show; $finish; end endmodule'''
def run(cmd, cwd=ROOT):
    p = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=180)
    if p.returncode:
        raise RuntimeError(p.stdout)
    return p.stdout
def rows(text):
    return [line.split()[1:] for line in text.splitlines() if line.startswith("ROW ")]
def main():
    source = HERE / "clocked_param_loop_e.sv"
    envelope = HERE / "clocked_param_loop_e.sv.json"
    with tempfile.NamedTemporaryFile(suffix=".json") as f:
        run(["python3", "extractors/sv/extract.py", "--top", HERE.name,
             "-o", f.name, str(source.relative_to(ROOT))])
        if Path(f.name).read_bytes() != envelope.read_bytes():
            raise RuntimeError("stale envelope")
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    for sim in ["iverilog"] + (["xrun"] if shutil.which("xrun") else []):
        with tempfile.TemporaryDirectory(prefix="sv-param-loop-") as work:
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
        print(f"{version}: 8 source rows MATCH")
    print("canonical E: retained parameter-bound loop admitted")
    print("clocked sv_structure: named descending-loop header refusal")
if __name__ == "__main__":
    main()
