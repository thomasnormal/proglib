#!/usr/bin/env python3
from pathlib import Path
import subprocess, tempfile
HERE = Path(__file__).resolve().parent
EXPECTED = [["0"], ["0"]]
TB = '''module tb; logic q; initial begin #1 $display("ROW %b",q); #1 $display("ROW %b",q); $finish; end initial_storage_e dut(.q(q)); endmodule'''
for sim in ("iverilog", "xrun"):
  with tempfile.TemporaryDirectory(prefix="sv-initial-") as td:
    tb = Path(td)/"tb.sv"; tb.write_text(TB)
    if sim == "iverilog":
      exe = Path(td)/"sim"
      subprocess.run(["iverilog","-g2012","-s","tb","-o",str(exe),str(HERE/"initial_storage_e.sv"),str(tb)], cwd=td, check=True)
      out = subprocess.run(["vvp",str(exe)], cwd=td, check=True, text=True, stdout=subprocess.PIPE).stdout
    else:
      out = subprocess.run(["xrun","-sv","-q","-timescale","1ns/1ps","-top","tb",str(HERE/"initial_storage_e.sv"),str(tb)], cwd=td, check=True, text=True, stdout=subprocess.PIPE).stdout
    rows = [line.split()[1:] for line in out.splitlines() if line.startswith("ROW ")]
    if rows != EXPECTED: raise SystemExit(f"{sim}: {rows} != {EXPECTED}")
    print(f"{sim}: 2 rows MATCH")
