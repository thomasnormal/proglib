#!/usr/bin/env python3
from pathlib import Path
import subprocess, tempfile

HERE = Path(__file__).resolve().parent
sources = [("plain_internal_edge_e", "plain_internal_edge_e.sv"),
           ("ff_internal_edge_e", "ff_internal_edge_e.sv")]
TB = '''module tb; logic clk,d,e,g,q; DUT dut(.*); task row(input logic nd, input logic ne);
  begin d=nd; e=ne; clk=1; #1 $display("ROW %b%b",g,q); clk=0; #1 $display("ROW %b%b",g,q); end
endtask
initial begin
  clk=0; d=0; e=0; #1 $display("ROW %b%b",g,q);
  row(0,0); row(1'bx,1); row(0,0); row(1'bz,1);
  row(0,0); row(1'bx,0); row(1,1); row(1'bx,0);
  row(1'bz,1); row(1,0); $finish; end endmodule'''
expected = ["xx", "0x", "0x", "x1", "x1", "01", "01", "z1", "z1", "01", "01", "x0", "x0", "11", "11", "x1", "x1", "z1", "z1", "10", "10"]
for top, filename in sources:
  for sim in ("iverilog", "xrun"):
    with tempfile.TemporaryDirectory(prefix="sv-r13-") as td:
      td = Path(td)
      tb = td / "tb.sv"
      tb.write_text(TB.replace("DUT", top))
      source = HERE / filename
      if sim == "iverilog":
        exe = td / "sim"
        subprocess.run(["iverilog", "-g2012", "-s", "tb", "-o", str(exe), str(source), str(tb)], cwd=td, check=True)
        out = subprocess.run(["vvp", str(exe)], cwd=td, check=True, text=True, stdout=subprocess.PIPE).stdout
      else:
        out = subprocess.run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "tb", str(source), str(tb)], cwd=td, check=True, text=True, stdout=subprocess.PIPE).stdout
      actual = [line.split()[1] for line in out.splitlines() if line.startswith("ROW ")]
      if actual != expected:
        raise SystemExit(f"{top}/{sim}: {actual} != {expected}")
      print(f"{top}/{sim}: {len(actual)} rows MATCH")
