#!/usr/bin/env python3
from pathlib import Path
import json, subprocess, tempfile
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]; ENV=HERE/'multi_clock_domain_e.sv.json'
rows=[json.loads(x) for x in subprocess.run(["python3","harness/sv/refusal_census.py","ordinary",str(ENV)],cwd=ROOT,check=True,text=True,stdout=subprocess.PIPE).stdout.splitlines()]
if not any(r.get("construct")=="Clock:multiple" for r in rows): raise SystemExit(f"missing Clock:multiple: {rows}")
TB='''module tb; logic aclk,bclk,d; logic x,y; multi_clock_domain_e dut(.aclk(aclk),.bclk(bclk),.d(d),.x(x),.y(y)); task show; $display("ROW %b %b %b %b %b",aclk,bclk,d,x,y); endtask initial begin aclk=0;bclk=0;d=0;#1 show; d=1;aclk=1;#1 show; aclk=0;bclk=1;#1 show; bclk=0;d=1'bx;aclk=1;#1 show; aclk=0;bclk=1'bx;d=1'bz;#1 show; bclk=0;aclk=1'bz;d=1;#1 show; aclk=0;bclk=0;d=0;#1 show; aclk=1;bclk=1;#1 show;$finish;end endmodule'''
expected=[["0","0","0","x","x"],["1","0","1","1","x"],["0","1","1","1","1"],["1","0","x","x","1"],["0","x","z","x","x"],["z","0","1","1","x"],["0","0","0","1","x"],["1","1","0","0","1"]]
for sim in ("iverilog","xrun"):
 with tempfile.TemporaryDirectory(prefix="sv-multiclk-") as td:
  tb=Path(td)/"tb.sv";tb.write_text(TB)
  if sim=="iverilog":
   exe=Path(td)/"sim";subprocess.run(["iverilog","-g2012","-s","tb","-o",str(exe),str(HERE/'multi_clock_domain_e.sv'),str(tb)],cwd=td,check=True);out=subprocess.run(["vvp",str(exe)],cwd=td,check=True,text=True,stdout=subprocess.PIPE).stdout
  else: out=subprocess.run(["xrun","-sv","-q","-timescale","1ns/1ps","-top","tb",str(HERE/'multi_clock_domain_e.sv'),str(tb)],cwd=td,check=True,text=True,stdout=subprocess.PIPE).stdout
  actual=[l.split()[1:] for l in out.splitlines() if l.startswith('ROW ')];
  if actual!=expected: raise SystemExit(f"{sim}: {actual} != {expected}")
  print(f"{sim}: 8 rows MATCH")
print("ordinary run2: exact Clock:multiple refusal; direct E receipt covers both clocks")
