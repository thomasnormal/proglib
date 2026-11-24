#!/usr/bin/env python3
"""Receipt for signed packed-vector bit selection."""
from pathlib import Path
import shutil, subprocess, tempfile
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]
SOURCE=HERE/'signed_bit_select_e.sv'; EXPECTED=['ROW 00000001 1','ROW 00000000 0','ROW x0110011 1']
TB='''module tb; logic signed [7:0] x; wire y; signed_select dut(x,y);
initial begin x=8'h01; #1 $display("ROW %b %b",x,y); x=0; #1 $display("ROW %b %b",x,y); x=8'bx0110011; #1 $display("ROW %b %b",x,y); $finish; end endmodule'''
def run(cmd,cwd=ROOT):
 p=subprocess.run(cmd,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=180)
 if p.returncode: raise RuntimeError(p.stdout)
 return p.stdout
def main():
 with tempfile.NamedTemporaryFile(suffix='.json') as f:
  run(['python3','extractors/sv/extract.py','--top','signed_select','-o',f.name,str(SOURCE.relative_to(ROOT))])
  if f.read()!=(HERE/(SOURCE.name+'.json')).read_bytes(): raise RuntimeError('stale envelope')
 run(['lake','env','lean',str(HERE/'agree.lean')])
 for sim in ['iverilog'] + (['xrun'] if shutil.which('xrun') else []):
  with tempfile.TemporaryDirectory(prefix='sv-signed-bit-') as d:
   tb=Path(d)/'tb.sv'; tb.write_text(TB)
   if sim=='iverilog':
    exe=str(Path(d)/'sim'); run(['iverilog','-g2012','-s','tb','-o',exe,str(SOURCE),str(tb)],d); out=run(['vvp',exe],d); ver=run(['iverilog','-V'],d).splitlines()[0]
   else:
    out=run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','tb',str(SOURCE),str(tb)],d); ver=run(['xrun','-version'],d).splitlines()[0]
  rows=[x for x in out.splitlines() if x.startswith('ROW ')]
  if rows!=EXPECTED: raise RuntimeError(f'{sim}: {rows} != {EXPECTED}')
  print(f'{ver}: 3 rows MATCH')
 print('canonical E: signed packed bit selection admitted')
if __name__=='__main__': main()
