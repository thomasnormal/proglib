#!/usr/bin/env python3
"""Receipt for plain any-edge event control, IEEE 1800-2023 §9.4.2."""
from pathlib import Path
import shutil, subprocess, tempfile
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]
SOURCE=HERE/'plain_event_any_edge_e.sv'; EXPECTED=['ROW 0 0','ROW 1 0','ROW 1 1','ROW 0 1','ROW 0 0']
TB='''module tb; logic clk,d; wire q; plain_event_any_edge_e dut(clk,d,q);
initial begin clk=0; d=0; #1 $display("ROW %b %b",d,q); d=1; #1 $display("ROW %b %b",d,q); clk=1; #1 $display("ROW %b %b",d,q); d=0; #1 $display("ROW %b %b",d,q); clk=0; #1 $display("ROW %b %b",d,q); $finish; end endmodule'''
def run(cmd,cwd=ROOT):
 p=subprocess.run(cmd,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=180)
 if p.returncode: raise RuntimeError(p.stdout)
 return p.stdout
def main():
 with tempfile.NamedTemporaryFile(suffix='.json') as f:
  run(['python3','extractors/sv/extract.py','--top',HERE.name,'-o',f.name,str(SOURCE.relative_to(ROOT))])
  if f.read()!=(HERE/(SOURCE.name+'.json')).read_bytes(): raise RuntimeError('stale envelope')
 run(['lake','env','lean',str(HERE/'agree.lean')])
 for sim in ['iverilog'] + (['xrun'] if shutil.which('xrun') else []):
  with tempfile.TemporaryDirectory(prefix='sv-any-edge-') as d:
   tb=Path(d)/'tb.sv'; tb.write_text(TB)
   if sim=='iverilog':
    exe=str(Path(d)/'sim'); run(['iverilog','-g2012','-s','tb','-o',exe,str(SOURCE),str(tb)],d); out=run(['vvp',exe],d); ver=run(['iverilog','-V'],d).splitlines()[0]
   else:
    out=run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','tb',str(SOURCE),str(tb)],d); ver=run(['xrun','-version'],d).splitlines()[0]
  rows=[x for x in out.splitlines() if x.startswith('ROW ')]
  if rows!=EXPECTED: raise RuntimeError(f'{sim}: {rows} != {EXPECTED}')
  print(f'{ver}: 5 rows MATCH')
 print('ordinary E: process retained as any-edge event; clocked sv_structure refusal is expected')
if __name__=='__main__': main()
