#!/usr/bin/env python3
from pathlib import Path
import subprocess, tempfile
HERE=Path(__file__).resolve().parent
TB='''module tb; logic clk,en,a,b; logic q; w11_mod dut(clk,en,a,b,q); initial begin clk=0; en=0; a=0; b=1; #0 $display("ROW t0 q=%b",q); #1 clk=1; #0 $display("ROW edge0 q=%b",q); #1 clk=0; en=1; #1 a=1; #1 clk=1; #0 $display("ROW edge1 q=%b",q); #1 $finish; end endmodule'''
def run(cmd,cwd):
 p=subprocess.run(cmd,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=180)
 if p.returncode: raise RuntimeError(p.stdout)
 return p.stdout
def main():
 run(['lake','env','lean',str(HERE/'agree.lean')],Path.cwd())
 with tempfile.TemporaryDirectory(prefix='sv-comb-default-') as w:
  tb=Path(w)/'tb.sv'; tb.write_text(TB)
  for sim in ('iverilog','xrun'):
   if sim=='iverilog':
    exe=str(Path(w)/'sim'); out=run(['iverilog','-g2012','-o',exe,str(HERE/'comb_default_override.sv'),str(tb)],Path(w)); out=run(['vvp',exe],Path(w))
   else: out=run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','tb',str(HERE/'comb_default_override.sv'),str(tb)],Path(w))
   print(sim, [x for x in out.splitlines() if x.startswith('ROW ')])
 print('E: Event:time-zero refusal pinned')
if __name__=='__main__': main()
