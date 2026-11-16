#!/usr/bin/env python3
from pathlib import Path
import shutil, subprocess, tempfile
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]
EXPECTED=[['1','0','x'],['0','1','1'],['1','0','1'],['x','1','1'],['0','1','1'],['z','0','1'],['1','0','1'],['0','1','1']]
def run(cmd,cwd=ROOT):
 p=subprocess.run(cmd,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=180)
 if p.returncode: raise RuntimeError(p.stdout)
 return p.stdout
def rows(s): return [x.split()[1:] for x in s.splitlines() if x.startswith('ROW ')]
def tb(): return '''module tb; logic clk,d; wire q; negedge_e dut(.clk(clk),.d(d),.q(q)); task show; $display("ROW %b %b %b",clk,d,q); endtask initial begin clk=1; d=0; #1 show; d=1; clk=0; #1 show; d=0; clk=1; #1 show; d=1; clk=1'bx; #1 show; clk=0; #1 show; d=0; clk=1'bz; #1 show; clk=1; #1 show; d=1; clk=0; #1 show; $finish; end endmodule\n'''
def main():
 run(['lake','env','lean',str(HERE/'agree.lean')])
 with tempfile.TemporaryDirectory() as w:
  t=Path(w)/'tb.sv'; t.write_text(tb()); exe=str(Path(w)/'sim'); run(['iverilog','-g2012','-s','tb','-o',exe,str(HERE/'negedge_e.sv'),str(t)],w); out=run(['vvp',exe],w)
  if rows(out)!=EXPECTED: raise RuntimeError(rows(out))
 print('canonical E negedge: 8 source rows MATCH Icarus Verilog 13.0')
 if shutil.which('xrun'):
  with tempfile.TemporaryDirectory() as w:
   t=Path(w)/'tb.sv'; t.write_text(tb()); out=run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','tb',str(HERE/'negedge_e.sv'),str(t)],w)
   if rows(out)!=EXPECTED: raise RuntimeError(rows(out))
  print('canonical E negedge: 8 source rows MATCH Xcelium 24.03-s004')
if __name__=='__main__': main()
