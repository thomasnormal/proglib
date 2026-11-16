#!/usr/bin/env python3
from pathlib import Path
import subprocess, tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [["x"], ["1"], ["1"], ["1"], ["1"], ["0"]]
TB = '''module tb; logic en,d; logic q;
always_latch_e dut(.en(en),.d(d),.q(q));
initial begin
 en=0; d=1; #1 $display("ROW %b",q);
 en=1; d=1; #1 $display("ROW %b",q);
 en=0; d=0; #1 $display("ROW %b",q);
 en=1'bx; d=0; #1 $display("ROW %b",q);
 en=1'bz; d=0; #1 $display("ROW %b",q);
 en=1; d=0; #1 $display("ROW %b",q); $finish;
end endmodule'''
for sim in ("iverilog", "xrun"):
  with tempfile.TemporaryDirectory(prefix="sv-latch-") as td:
    tb = Path(td)/"tb.sv"; tb.write_text(TB)
    if sim == "iverilog":
      exe = Path(td)/"sim"
      subprocess.run(["iverilog","-g2012","-s","tb","-o",str(exe),str(HERE/"always_latch_e.sv"),str(tb)], cwd=td, check=True)
      out = subprocess.run(["vvp",str(exe)], cwd=td, check=True, text=True, stdout=subprocess.PIPE).stdout
    else:
      out = subprocess.run(["xrun","-sv","-q","-timescale","1ns/1ps","-top","tb",str(HERE/"always_latch_e.sv"),str(tb)], cwd=td, check=True, text=True, stdout=subprocess.PIPE).stdout
    rows = [line.split()[1:] for line in out.splitlines() if line.startswith("ROW ")]
    if rows != EXPECTED: raise SystemExit(f"{sim}: {rows} != {EXPECTED}")
    print(f"{sim}: 6 rows MATCH")
