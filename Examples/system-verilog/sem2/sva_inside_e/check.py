#!/usr/bin/env python3
"""Clean-room regression for SVA inside wildcard lowering (IEEE 1800-2023 §11.4.13)."""
from pathlib import Path
import subprocess
import tempfile
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]
def main():
 p=subprocess.run(['lake','build','Examples.«system-verilog».sem2.sva_inside_e.agree'],cwd=ROOT,text=True,capture_output=True)
 if p.returncode: raise RuntimeError(p.stdout+p.stderr)
 with tempfile.TemporaryDirectory(prefix='sv-sva-inside-', dir='/var/tmp') as work:
  tb=Path(work)/'tb.sv'
  tb.write_text('''module tb; logic clk=0; logic [3:0] a; sva_inside_e dut(clk,a); always #1 clk=~clk; initial begin a=4'b0001; #2 a=4'b0011; #2 a=4'b0010; #2 $finish; end endmodule''')
  i=subprocess.run(['iverilog','-g2012','-o',str(Path(work)/'a.out'),str(HERE/'sva_inside_e.sv'),str(tb)],cwd=work,text=True,capture_output=True,check=False,timeout=60)
  if i.returncode == 0 or 'inside' not in i.stderr:
   raise RuntimeError('Icarus unexpectedly compiled the SVA inside fixture; its unsupported boundary changed')
  p=subprocess.run(['xrun','-sv','-q','-assert','-timescale','1ns/1ps','-top','tb',str(HERE/'sva_inside_e.sv'),str(tb)],cwd=work,text=True,capture_output=True,check=False,timeout=60)
  if p.returncode == 0 or 'Assertion tb.dut.ap has failed' not in p.stdout:
   raise RuntimeError('Xcelium did not show the expected wildcard-inside pass/fail boundary:\n'+p.stdout)
 print('SVA inside 4\'b0x01 retained as a four-bit wildcard literal; Icarus 13.0 has no oracle (unsupported); Xcelium 24.03-s004 accepts 0001 and 0011 and rejects 0010')
if __name__=='__main__': main()
