#!/usr/bin/env python3
"""Receipt for a source-shaped implicit event-control refusal."""
from pathlib import Path
import shutil
import subprocess
import tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [["q=0"], ["q=0"], ["q=1"], ["q=0"], ["q=x"], ["q=z"], ["q=1"], ["q=0"]]

def run(cmd, cwd=ROOT):
    p = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=180)
    if p.returncode:
        raise RuntimeError(p.stdout)
    return p.stdout

def rows(text):
    return [line.split()[2:] for line in text.splitlines() if line.startswith("ROW ")]

def tb(top):
    return f'''module tb; logic clk,d; wire q; {top} dut(clk,d,q); initial begin
clk=0; d=0; #1 $display("ROW 0 q=%b",q);
d=1; #1 $display("ROW 1 q=%b",q);
clk=1; #1 $display("ROW 2 q=%b",q);
clk=0; d=0; #1 $display("ROW 3 q=%b",q);
clk=1'bx; d=1'bx; #1 $display("ROW 4 q=%b",q);
clk=1'bz; d=1'bz; #1 $display("ROW 5 q=%b",q);
clk=0; d=1; #1 $display("ROW 6 q=%b",q);
clk=1; d=0; #1 $display("ROW 7 q=%b",q); $finish; end endmodule
'''

def main():
    top = HERE.name
    source = HERE / f"{top}.sv"
    with tempfile.NamedTemporaryFile(suffix=".json") as f:
        run(["python3", "extractors/sv/extract.py", "--top", top, "-o", f.name,
             str(source.relative_to(ROOT))])
        if Path(f.name).read_bytes() != (HERE / f"{top}.sv.json").read_bytes():
            raise RuntimeError("stale envelope")
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    print("extractor: envelope regenerates byte-identically")
    print("E: REFUSED Clock:implicit; no E row claimed")
    simulators = ["iverilog"] + (["xrun"] if shutil.which("xrun") else [])
    for sim in simulators:
        with tempfile.TemporaryDirectory(prefix="sv-implicit-event-") as work:
            tb_path = Path(work) / "tb.sv"; tb_path.write_text(tb(top))
            if sim == "iverilog":
                exe = str(Path(work) / "sim")
                run(["iverilog", "-g2012", "-s", "tb", "-o", exe, str(source), str(tb_path)], work)
                out = run(["vvp", exe], work)
            else:
                out = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "tb", str(source), str(tb_path)], work)
        actual = rows(out)
        if actual != EXPECTED:
            raise RuntimeError(f"{sim}: {actual} != {EXPECTED}")
        version = run(["iverilog", "-V"] if sim == "iverilog" else ["xrun", "-version"]).splitlines()[0]
        print(f"{version}: 8 source rows MATCH simulator")

if __name__ == "__main__":
    main()
