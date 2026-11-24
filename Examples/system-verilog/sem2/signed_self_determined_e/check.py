#!/usr/bin/env python3
"""Receipt for signed self-determined comparison width propagation."""
from pathlib import Path
import shutil, subprocess, tempfile
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]
SOURCE=HERE/'signed_self_determined_e.sv'; EXPECTED=['ROW 1111 0000 1 1','ROW 1000 0111 1 1','ROW xxxx 0001 1 x','ROW 1111 0000 0 0']
TB='''module tb; logic signed [3:0] a,b; logic en; wire y; signed_self_determined dut(a,b,en,y);
initial begin a=-4'sd1; b=4'sd0; en=1; #1 $display("ROW %b %b %b %b",a,b,en,y); a=4'sh8; b=4'sd7; #1 $display("ROW %b %b %b %b",a,b,en,y); a=4'bx; b=1; #1 $display("ROW %b %b %b %b",a,b,en,y); en=0; a=-1; b=0; #1 $display("ROW %b %b %b %b",a,b,en,y); $finish; end endmodule'''
def run(cmd,cwd=ROOT):
 p=subprocess.run(cmd,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=180)
 if p.returncode: raise RuntimeError(p.stdout)
 return p.stdout
def main():
 with tempfile.NamedTemporaryFile(suffix='.json') as f:
  run(['python3','extractors/sv/extract.py','--top','signed_self_determined','-o',f.name,str(SOURCE.relative_to(ROOT))])
  if f.read()!=(HERE/(SOURCE.name+'.json')).read_bytes(): raise RuntimeError('stale envelope')
 run(['lake','env','lean',str(HERE/'agree.lean')])
 for sim in ['iverilog'] + (['xrun'] if shutil.which('xrun') else []):
  with tempfile.TemporaryDirectory(prefix='sv-signed-self-') as d:
   tb=Path(d)/'tb.sv'; tb.write_text(TB)
   if sim=='iverilog':
    exe=str(Path(d)/'sim'); run(['iverilog','-g2012','-s','tb','-o',exe,str(SOURCE),str(tb)],d); out=run(['vvp',exe],d); ver=run(['iverilog','-V'],d).splitlines()[0]
   else:
    out=run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','tb',str(SOURCE),str(tb)],d); ver=run(['xrun','-version'],d).splitlines()[0]
  rows=[x for x in out.splitlines() if x.startswith('ROW ')]
  if rows!=EXPECTED: raise RuntimeError(f'{sim}: {rows} != {EXPECTED}')
  print(f'{ver}: 4 rows MATCH')
 print('canonical E: signed comparison uses self-determined operand width')
if __name__=='__main__': main()
