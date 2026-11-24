#!/usr/bin/env python3
from pathlib import Path
import shutil, subprocess, tempfile
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]
SOURCE=HERE/'explicit_cast_signed_param_e.sv'; EXPECTED=['ROW 1111 11111111 1010 00001010','ROW 1000 11111000 0111 00000111','ROW x01z xxxxx01z 1010 00001010']
TB='''module tb; logic signed [3:0] x; logic [3:0] b; wire [7:0] ys,yb; explicit_cast_signed_param_e #(.W(8)) dut(x,b,ys,yb);
initial begin x=-1; b=4'ha; #1 $display("ROW %b %b %b %b",x,ys,b,yb); x=-8; b=7; #1 $display("ROW %b %b %b %b",x,ys,b,yb); x=4'bx01z; b=4'ha; #1 $display("ROW %b %b %b %b",x,ys,b,yb); $finish; end endmodule'''
def run(cmd,cwd=ROOT):
 p=subprocess.run(cmd,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=180)
 if p.returncode: raise RuntimeError(p.stdout)
 return p.stdout
def main():
 with tempfile.NamedTemporaryFile(suffix='.json') as f:
  run(['python3','extractors/sv/extract.py','--top','explicit_cast_signed_param_e','-o',f.name,str(SOURCE.relative_to(ROOT))])
  if f.read()!=(HERE/(SOURCE.name+'.json')).read_bytes(): raise RuntimeError('stale envelope')
 run(['lake','env','lean',str(HERE/'agree.lean')])
 for sim in ['iverilog'] + (['xrun'] if shutil.which('xrun') else []):
  with tempfile.TemporaryDirectory(prefix='sv-param-cast-') as d:
   tb=Path(d)/'tb.sv'; tb.write_text(TB)
   if sim=='iverilog':
    exe=str(Path(d)/'sim'); run(['iverilog','-g2012','-s','tb','-o',exe,str(SOURCE),str(tb)],d); out=run(['vvp',exe],d); ver=run(['iverilog','-V'],d).splitlines()[0]
   else:
    out=run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','tb',str(SOURCE),str(tb)],d); ver=run(['xrun','-version'],d).splitlines()[0]
  rows=[x for x in out.splitlines() if x.startswith('ROW ')]
  if rows!=EXPECTED: raise RuntimeError(f'{sim}: {rows} != {EXPECTED}')
  print(f'{ver}: 3 rows MATCH')
if __name__=='__main__': main()
