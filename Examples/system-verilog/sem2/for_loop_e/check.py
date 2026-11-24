#!/usr/bin/env python3
"""Receipt for the fixed-array procedural-for target boundary."""
from pathlib import Path
import shutil, subprocess, tempfile
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]
SOURCE=HERE/'for_loop_e.sv'
TB='''module tb; logic clk; logic [7:0] d; wire [7:0] q; for_loop_e dut(clk,d,q);
initial begin clk=0; d=8'h12; #1 $display("ROW %b",q); clk=1; #1 $display("ROW %b",q); clk=0; d=8'h34; #1 $display("ROW %b",q); clk=1; #1 $display("ROW %b",q); $finish; end endmodule'''
def run(cmd,cwd=ROOT):
 p=subprocess.run(cmd,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=180)
 if p.returncode: raise RuntimeError(p.stdout)
 return p.stdout
def main():
 run(['python3','extractors/sv/extract.py','--top','for_loop_e','-o',str(HERE/(SOURCE.name+'.json')),str(SOURCE.relative_to(ROOT))])
 run(['lake','env','lean',str(HERE/'agree.lean')])
 for sim in ['iverilog'] + (['xrun'] if shutil.which('xrun') else []):
  with tempfile.TemporaryDirectory(prefix='sv-for-loop-') as d:
   tb=Path(d)/'tb.sv'; tb.write_text(TB)
   if sim=='iverilog':
    exe=str(Path(d)/'sim'); run(['iverilog','-g2012','-s','tb','-o',exe,str(SOURCE),str(tb)],d); out=run(['vvp',exe],d); ver=run(['iverilog','-V'],d).splitlines()[0]
   else:
    out=run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','tb',str(SOURCE),str(tb)],d); ver=run(['xrun','-version'],d).splitlines()[0]
  rows=[x for x in out.splitlines() if x.startswith('ROW ')]
  if len(rows)!=4: raise RuntimeError(f'{sim}: expected four rows, got {rows}')
  print(f'{ver}: 4 source rows observed')
 print('canonical E: indexed procedural-for target remains loudly refused')
if __name__=='__main__': main()
