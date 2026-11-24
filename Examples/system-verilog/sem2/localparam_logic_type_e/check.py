#!/usr/bin/env python3
from pathlib import Path
import shutil, subprocess, tempfile
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]
SOURCE=HERE/'localparam_logic_type_e.sv'; EXPECTED=['ROW 0000 0001','ROW 1010 1011','ROW 1111 1110','ROW xxxx xxxx']
TB='''module tb; logic [3:0] a; wire [3:0] y; localparam_logic_type_e dut(a,y);
initial begin a=0; #1 $display("ROW %b %b",a,y); a=4'ha; #1 $display("ROW %b %b",a,y); a=4'hf; #1 $display("ROW %b %b",a,y); a=4'hx; #1 $display("ROW %b %b",a,y); $finish; end endmodule'''
def run(cmd,cwd=ROOT):
 p=subprocess.run(cmd,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=180)
 if p.returncode: raise RuntimeError(p.stdout)
 return p.stdout
def main():
 with tempfile.NamedTemporaryFile(suffix='.json') as f:
  run(['python3','extractors/sv/extract.py','--top','localparam_logic_type_e','-o',f.name,str(SOURCE.relative_to(ROOT))])
  if f.read()!=(HERE/(SOURCE.name+'.json')).read_bytes(): raise RuntimeError('stale envelope')
 run(['lake','env','lean',str(HERE/'agree.lean')])
 for sim in ['iverilog'] + (['xrun'] if shutil.which('xrun') else []):
  with tempfile.TemporaryDirectory(prefix='sv-lp-logic-') as d:
   tb=Path(d)/'tb.sv'; tb.write_text(TB)
   if sim=='iverilog':
    exe=str(Path(d)/'sim'); run(['iverilog','-g2012','-s','tb','-o',exe,str(SOURCE),str(tb)],d); out=run(['vvp',exe],d); ver=run(['iverilog','-V'],d).splitlines()[0]
   else:
    out=run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','tb',str(SOURCE),str(tb)],d); ver=run(['xrun','-version'],d).splitlines()[0]
  rows=[x for x in out.splitlines() if x.startswith('ROW ')]
  if rows!=EXPECTED: raise RuntimeError(f'{sim}: {rows} != {EXPECTED}')
  print(f'{ver}: 4 source rows MATCH')
 print('sv_structure: logic-typed localparam remains a clocked-profile refusal')
if __name__=='__main__': main()
