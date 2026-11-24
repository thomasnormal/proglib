#!/usr/bin/env python3
from pathlib import Path
import shutil, subprocess, tempfile
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]
SOURCE=HERE/'signed_member_e.sv'; EXPECTED=['ROW 11111111 1','ROW 00000000 0','ROW 01111111 0','ROW xxxxxxxx x']
TB='''module tb; logic signed [7:0] a; wire lt; signed_member_e dut(a,lt);
initial begin a=-1; #1 $display("ROW %b %b",a,lt); a=0; #1 $display("ROW %b %b",a,lt); a=127; #1 $display("ROW %b %b",a,lt); a=8'bx; #1 $display("ROW %b %b",a,lt); $finish; end endmodule'''
def run(cmd,cwd=ROOT):
 p=subprocess.run(cmd,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=180)
 if p.returncode: raise RuntimeError(p.stdout)
 return p.stdout
def main():
 with tempfile.NamedTemporaryFile(suffix='.json') as f:
  run(['python3','extractors/sv/extract.py','--top','signed_member_e','-o',f.name,str(SOURCE.relative_to(ROOT))])
  if f.read()!=(HERE/(SOURCE.name+'.json')).read_bytes(): raise RuntimeError('stale envelope')
 run(['lake','env','lean',str(HERE/'agree.lean')])
 for sim in ['iverilog'] + (['xrun'] if shutil.which('xrun') else []):
  with tempfile.TemporaryDirectory(prefix='sv-signed-member-') as d:
   tb=Path(d)/'tb.sv'; tb.write_text(TB)
   if sim=='iverilog':
    exe=str(Path(d)/'sim'); run(['iverilog','-g2012','-s','tb','-o',exe,str(SOURCE),str(tb)],d); out=run(['vvp',exe],d); ver=run(['iverilog','-V'],d).splitlines()[0]
   else:
    out=run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','tb',str(SOURCE),str(tb)],d); ver=run(['xrun','-version'],d).splitlines()[0]
  rows=[x for x in out.splitlines() if x.startswith('ROW ')]
  if rows!=EXPECTED: raise RuntimeError(f'{sim}: {rows} != {EXPECTED}')
  print(f'{ver}: 4 rows MATCH')
if __name__=='__main__': main()
