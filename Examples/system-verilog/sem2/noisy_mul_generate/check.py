#!/usr/bin/env python3
from pathlib import Path
import shutil, subprocess, tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCE = HERE / "noisy_mul_generate.sv"
EXPECTED = [
    "ROW N=2 a=0 b=0 f=0 p=0000",
    "ROW N=2 a=3 b=3 f=0 p=1001",
    "ROW N=3 a=7 b=7 f=0 p=110001",
    "ROW N=4 a=15 b=15 f=0 p=11100001",
]
TB = '''module tb;
  logic [1:0] a2,b2; logic [11:0] f2; wire [3:0] p2;
  logic [2:0] a3,b3; logic [32:0] f3; wire [5:0] p3;
  logic [3:0] a4,b4; logic [60:0] f4; wire [7:0] p4;
  noisy_mul #(.N(2)) d2(.a(a2),.b(b2),.f(f2),.p(p2));
  noisy_mul #(.N(3)) d3(.a(a3),.b(b3),.f(f3),.p(p3));
  noisy_mul #(.N(4)) d4(.a(a4),.b(b4),.f(f4),.p(p4));
  initial begin
    a2=0; b2=0; f2=0; #1 $display("ROW N=2 a=%0d b=%0d f=%0d p=%b",a2,b2,f2,p2);
    a2=3; b2=3; #1 $display("ROW N=2 a=%0d b=%0d f=%0d p=%b",a2,b2,f2,p2);
    a3=7; b3=7; f3=0; #1 $display("ROW N=3 a=%0d b=%0d f=%0d p=%b",a3,b3,f3,p3);
    a4=15; b4=15; f4=0; #1 $display("ROW N=4 a=%0d b=%0d f=%0d p=%b",a4,b4,f4,p4);
    $finish;
  end
endmodule'''
def run(cmd, cwd=ROOT):
    p = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=180)
    if p.returncode:
        raise RuntimeError(p.stdout)
    return p.stdout
def main():
    with tempfile.TemporaryDirectory(prefix="sv-noisy-mul-") as d:
        tb = Path(d) / "tb.sv"; tb.write_text(TB)
        for sim in ["iverilog"] + (["xrun"] if shutil.which("xrun") else []):
            if sim == "iverilog":
                exe = str(Path(d) / "sim")
                run(["iverilog", "-g2012", "-s", "tb", "-o", exe,
                     str(SOURCE), str(tb)], d)
                out = run(["vvp", exe], d)
                version = run(["iverilog", "-V"], d).splitlines()[0]
            else:
                out = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                           "-top", "tb", str(SOURCE), str(tb)], d)
                version = run(["xrun", "-version"], d).splitlines()[0]
            rows = [line for line in out.splitlines() if line.startswith("ROW ")]
            if rows != EXPECTED:
                raise RuntimeError(f"{sim}: {rows} != {EXPECTED}")
            print(f"{version}: 4 rows MATCH")
if __name__ == "__main__":
    main()
