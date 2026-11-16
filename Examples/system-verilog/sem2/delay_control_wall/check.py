#!/usr/bin/env python3
from pathlib import Path
import json, subprocess, tempfile
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]; ENV=HERE/'delay_control_wall.sv.json'
rows=[json.loads(x) for x in subprocess.run(["python3","harness/sv/refusal_census.py","ordinary",str(ENV)],cwd=ROOT,check=True,text=True,stdout=subprocess.PIPE).stdout.splitlines()]
if not any(r.get("construct")=="TimedStatement:DelayControl" and r.get("function")=="parsePStmt" for r in rows): raise SystemExit(f"missing delay refusal: {rows}")
TB='''module tb; logic clk,d,q; event_always_repro dut(.clk(clk),.d(d),.q(q)); initial begin clk=0;d=0;#1 $display("ROW %b",q); d=1;clk=1;#2 $display("ROW %b",q); clk=0;d=1'bx;#1 $display("ROW %b",q); clk=1;#2 $display("ROW %b",q); $finish; end endmodule'''
expected=[["x"],["1"],["1"],["x"]]
for sim in ("iverilog","xrun"):
 with tempfile.TemporaryDirectory(prefix="sv-delay-") as td:
  tb=Path(td)/"tb.sv";tb.write_text(TB)
  if sim=="iverilog":
   exe=Path(td)/"sim";subprocess.run(["iverilog","-g2012","-s","tb","-o",str(exe),str(HERE/'delay_control_wall.sv'),str(tb)],cwd=td,check=True);out=subprocess.run(["vvp",str(exe)],cwd=td,check=True,text=True,stdout=subprocess.PIPE).stdout
  else: out=subprocess.run(["xrun","-sv","-q","-timescale","1ns/1ps","-top","tb",str(HERE/'delay_control_wall.sv'),str(tb)],cwd=td,check=True,text=True,stdout=subprocess.PIPE).stdout
  actual=[l.split()[1:] for l in out.splitlines() if l.startswith('ROW ')];
  if actual!=expected: raise SystemExit(f"{sim}: {actual} != {expected}")
  print(f"{sim}: 4 rows MATCH")
print("ordinary census: exact TimedStatement:DelayControl refusal")
