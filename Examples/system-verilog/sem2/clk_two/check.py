#!/usr/bin/env python3
"""Differential receipt for the two-clock ordinary-route refusal."""

from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [
    ["0", "0", "0", "x", "x"], ["1", "0", "1", "1", "x"],
    ["0", "1", "1", "1", "1"], ["1", "0", "x", "x", "1"],
    ["0", "x", "z", "x", "x"], ["z", "0", "1", "1", "x"],
    ["0", "0", "0", "1", "x"], ["1", "1", "0", "0", "1"],
]


def run(cmd, cwd=ROOT, check=True):
    p = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=180)
    if check and p.returncode:
        raise RuntimeError(p.stdout)
    return p


def rows(text):
    return [line.split()[1:] for line in text.splitlines()
            if line.startswith("ROW ")]


def tb(top):
    return f'''`timescale 1ns/1ps
module tb;
 logic clk1,clk2,d; wire a,b;
 {top} dut(.clk1(clk1),.clk2(clk2),.d(d),.a(a),.b(b));
 task show; $display("ROW %b %b %b %b %b",clk1,clk2,d,a,b); endtask
 initial begin
  clk1=0; clk2=0; d=0; #1 show;
  d=1; clk1=1; #1 show;
  clk1=0; clk2=1; #1 show;
  clk2=0; d=1'bx; clk1=1; #1 show;
  clk1=0; clk2=1'bx; d=1'bz; #1 show;
  clk2=0; clk1=1'bz; d=1; #1 show;
  clk1=0; clk2=0; d=0; #1 show;
  clk1=1; clk2=1; #1 show;
  $finish;
 end
endmodule
'''.replace('+', '')


def refusal_receipt():
    source = HERE / f"{HERE.name}.sv"
    envelope = HERE / f"{HERE.name}.sv.json"
    with tempfile.NamedTemporaryFile(suffix=".json") as f:
        run(["python3", "extractors/sv/extract.py", "--top", HERE.name,
             "-o", f.name, str(source.relative_to(ROOT))])
        if Path(f.name).read_bytes() != envelope.read_bytes():
            raise RuntimeError("stale envelope")
    with tempfile.NamedTemporaryFile("w", suffix=".lean") as f:
        f.write("import LeanModels.Sv.Ingest2\n")
        f.write(f'load_design_sv2 clkTwoCheck from "{envelope}"\n')
        f.flush()
        p = run(["lake", "env", "lean", f.name], check=False)
    if p.returncode == 0 or "Clock:multiple" not in p.stdout:
        raise RuntimeError("ordinary loader did not refuse Clock:multiple:\n" + p.stdout)
    print("extractor: envelope regenerates byte-identically")
    print("ordinary loader: REFUSED Clock:multiple")


def simulator_receipt(sim):
    source = HERE / f"{HERE.name}.sv"
    with tempfile.TemporaryDirectory(prefix="sv-clk-two-") as work:
        tb_path = Path(work) / "tb.sv"
        tb_path.write_text(tb(HERE.name))
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
    version = run(["iverilog", "-V"] if sim == "iverilog"
                  else ["xrun", "-version"]).stdout.splitlines()[0]
    print(f"{version}: 8 source rows MATCH simulator")


def main():
    refusal_receipt()
    simulator_receipt("iverilog")
    if shutil.which("xrun"):
        simulator_receipt("xrun")


if __name__ == "__main__":
    main()
