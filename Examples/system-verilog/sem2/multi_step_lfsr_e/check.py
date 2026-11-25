#!/usr/bin/env python3
from pathlib import Path
import shutil, subprocess, tempfile
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]
EXPECTED=["ROW 0 0 00000001","ROW 1 1 01100100","ROW 0 1 01100100","ROW 1 1 10010011","ROW 0 1 10010011","ROW 1 1 00000011","ROW 0 1 00000011","ROW 1 1 10101100"]
def run(a,cwd=ROOT):
 p=subprocess.run(a,cwd=cwd,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,timeout=180)
 if p.returncode: raise RuntimeError(p.stdout)
 return p.stdout
def main():
 with tempfile.NamedTemporaryFile(suffix='.json') as f:
  run(['python3','extractors/sv/extract.py','--top',HERE.name,'--retain-proc-rewrites','-o',f.name,str((HERE/(HERE.name+'.sv')).relative_to(ROOT))])
  if Path(f.name).read_bytes()!=(HERE/(HERE.name+'.sv.json')).read_bytes(): raise RuntimeError('stale envelope')
 run(['lake','env','lean',str(HERE/'agree.lean')]); print('ordinary E: generated indexed-select processes admitted, 8 rows MATCH')
 tb='''module tb; logic clk,rstn,en; wire [7:0] state; multi_step_lfsr_e #(.WIDTH(8),.TAPS(8'hb8)) dut(clk,rstn,en,state);
 initial begin clk=0;rstn=0;en=0;#1 $display("ROW 0 0 %b",state); rstn=1;en=1; clk=1;#1 $display("ROW 1 1 %b",state); clk=0;#1 $display("ROW 0 1 %b",state);clk=1;#1 $display("ROW 1 1 %b",state);clk=0;#1 $display("ROW 0 1 %b",state);clk=1;#1 $display("ROW 1 1 %b",state);clk=0;#1 $display("ROW 0 1 %b",state);clk=1;#1 $display("ROW 1 1 %b",state);$finish;end endmodule'''
 src=str(HERE/(HERE.name+'.sv'))
 for sim in ['iverilog']+(['xrun'] if shutil.which('xrun') else []):
  with tempfile.TemporaryDirectory(prefix='sv-multi-step-lfsr-') as w:
   p=Path(w)/'tb.sv';p.write_text(tb)
   if sim=='iverilog':
    exe=str(Path(w)/'sim');run(['iverilog','-g2012','-s','tb','-o',exe,src,str(p)],w);actual=[x for x in run(['vvp',exe],w).splitlines() if x.startswith('ROW ')]
    ver=run(['iverilog','-V'],w).splitlines()[0]
   else:
    actual=[x for x in run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','tb',src,str(p)],w).splitlines() if x.startswith('ROW ')];ver=run(['xrun','-version'],w).splitlines()[0]
  if actual!=EXPECTED: raise RuntimeError(f'{sim}: {actual!r}')
  print(f'{ver}: 8 rows MATCH E')
if __name__=='__main__':main()
