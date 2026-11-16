#!/usr/bin/env python3
from pathlib import Path
import subprocess,tempfile
HERE=Path(__file__).resolve().parent
ENV=HERE/'child_instance_e.sv.json'
ordinary = subprocess.run(['python3','harness/sv/refusal_census.py','ordinary',str(ENV)], cwd=HERE.parents[3], check=True, text=True, stdout=subprocess.PIPE).stdout
if '"refusals": 0' not in ordinary:
 raise SystemExit('ordinary hierarchical E census still refuses nested child instances: '+ordinary)
TB='''module tb; logic clk,rst_n,d,q; child_instance_scan dut(.clk(clk),.rst_n(rst_n),.d(d),.q(q)); initial begin clk=0;rst_n=0;d=0;#1 $display("ROW %b",q);clk=1;rst_n=1;d=1;#1 $display("ROW %b",q);clk=0;d=0;#1 $display("ROW %b",q);clk=1;#1 $display("ROW %b",q);$finish;end endmodule'''
expected=[["0"],["0"],["0"],["1"]]
for sim in ('iverilog','xrun'):
 with tempfile.TemporaryDirectory(prefix='sv-child-e-') as td:
  tb=Path(td)/'tb.sv';tb.write_text(TB)
  if sim=='iverilog':
   exe=Path(td)/'sim';subprocess.run(['iverilog','-g2012','-s','tb','-o',str(exe),str(HERE/'child_instance_e.sv'),str(tb)],cwd=td,check=True);out=subprocess.run(['vvp',str(exe)],cwd=td,check=True,text=True,stdout=subprocess.PIPE).stdout
  else: out=subprocess.run(['xrun','-sv','-q','-timescale','1ns/1ps','-top','tb',str(HERE/'child_instance_e.sv'),str(tb)],cwd=td,check=True,text=True,stdout=subprocess.PIPE).stdout
  actual=[l.split()[1:] for l in out.splitlines() if l.startswith('ROW ')];
  if actual!=expected: raise SystemExit(f'{sim}: {actual} != {expected}')
  print(f'{sim}: 4 rows MATCH')
