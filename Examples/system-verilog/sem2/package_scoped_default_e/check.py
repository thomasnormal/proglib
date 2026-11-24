#!/usr/bin/env python3
from pathlib import Path
import shutil, subprocess, tempfile
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]
SOURCE=HERE/'package_scoped_default_e.sv'; EXPECTED=['ROW 0001 0001','ROW 000a 000a','ROW xxxx xxxx']
TB='''module tb; logic [15:0] i; wire [15:0] o; package_scoped_default_e dut(i,o);
initial begin i=16'h1; #1 $display("ROW %h %h",i,o); i=16'ha; #1 $display("ROW %h %h",i,o); i=16'hx; #1 $display("ROW %h %h",i,o); $finish; end endmodule'''
def run(cmd,cwd=ROOT):
 p=subprocess.run(cmd,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=180)
 if p.returncode: raise RuntimeError(p.stdout)
 return p.stdout
def main():
 with tempfile.NamedTemporaryFile(suffix='.json') as f:
  run(['python3','extractors/sv/extract.py','--top','package_scoped_default_e','-o',f.name,str(SOURCE.relative_to(ROOT))])
  if f.read()!=(HERE/(SOURCE.name+'.json')).read_bytes(): raise RuntimeError('stale envelope')
 run(['lake','env','lean',str(HERE/'agree.lean')])
 for sim in ['iverilog'] + (['xrun'] if shutil.which('xrun') else []):
  with tempfile.TemporaryDirectory(prefix='sv-pkg-default-') as d:
   tb=Path(d)/'tb.sv'; tb.write_text(TB)
   if sim=='iverilog':
    exe=str(Path(d)/'sim'); run(['iverilog','-g2012','-s','tb','-o',exe,str(SOURCE),str(tb)],d); out=run(['vvp',exe],d); ver=run(['iverilog','-V'],d).splitlines()[0]
   else:
    out=run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','tb',str(SOURCE),str(tb)],d); ver=run(['xrun','-version'],d).splitlines()[0]
  rows=[x for x in out.splitlines() if x.startswith('ROW ')]
  if rows!=EXPECTED: raise RuntimeError(f'{sim}: {rows} != {EXPECTED}')
  print(f'{ver}: 3 rows MATCH')
if __name__=='__main__': main()
