#!/usr/bin/env python3
from pathlib import Path
import subprocess, tempfile, json
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
sources = [("plain_internal_edge_e", "plain_internal_edge_e.sv"),
           ("ff_internal_edge_e", "ff_internal_edge_e.sv")]
TB = '''module tb; logic clk,d,g,q; DUT dut(.*); initial begin
  clk=0; d=0; #1 $display("ROW %b%b",g,q);
  d=1; clk=1; #1 $display("ROW %b%b",g,q);
  clk=0; #1 $display("ROW %b%b",g,q);
  d=1'bx; clk=1'bx; #1 $display("ROW %b%b",g,q);
  d=1'bz; clk=1'bz; #1 $display("ROW %b%b",g,q);
  d=1'bx; clk=1; #1 $display("ROW %b%b",g,q);
  clk=0; #1 $display("ROW %b%b",g,q);
  d=1'bz; clk=1'bz; #1 $display("ROW %b%b",g,q);
  $finish; end endmodule'''
expected = ["xx", "11", "11", "x1", "x1", "x1", "x1", "z1"]
for top, filename in sources:
  for sim in ("iverilog", "xrun"):
    with tempfile.TemporaryDirectory(prefix="sv-r13-") as td:
      tb = Path(td)/"tb.sv"; tb.write_text(TB.replace("DUT", top))
      source = HERE / filename
      if sim == "iverilog":
        exe = Path(td)/"sim"
        subprocess.run(["iverilog", "-g2012", "-s", "tb", "-o", str(exe), str(source), str(tb)], cwd=td, check=True)
        out = subprocess.run(["vvp", str(exe)], cwd=td, check=True, text=True, stdout=subprocess.PIPE).stdout
      else:
        out = subprocess.run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "tb", str(source), str(tb)], cwd=td, check=True, text=True, stdout=subprocess.PIPE).stdout
      actual = [line.split()[1] for line in out.splitlines() if line.startswith("ROW ")]
      if actual != expected:
        raise SystemExit(f"{top}/{sim}: {actual} != {expected}")
      print(f"{top}/{sim}: 8 rows MATCH")
