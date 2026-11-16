#!/usr/bin/env python3
from pathlib import Path
import json, subprocess, tempfile
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]; ENV=HERE/'hierarchical_value_wall.sv.json'
rows=[json.loads(x) for x in subprocess.run(["python3","harness/sv/refusal_census.py","ordinary",str(ENV)],cwd=ROOT,check=True,text=True,stdout=subprocess.PIPE).stdout.splitlines()]
if not any(r.get("construct")=="HierarchicalValueExpression" and r.get("function")=="parsePExpr" for r in rows): raise SystemExit(f"missing hierarchy refusal: {rows}")
TB='''module tb; logic result; hierarchical_value_repro dut(.result(result)); initial begin #1 $display("ROW %b",result); #1 $display("ROW %b",result); $finish; end endmodule'''
expected=[["1"],["1"]]
for sim in ("iverilog","xrun"):
 with tempfile.TemporaryDirectory(prefix="sv-hier-value-") as td:
  tb=Path(td)/"tb.sv";tb.write_text(TB)
  if sim=="iverilog":
   exe=Path(td)/"sim";subprocess.run(["iverilog","-g2012","-s","tb","-o",str(exe),str(HERE/'hierarchical_value_wall.sv'),str(tb)],cwd=td,check=True);out=subprocess.run(["vvp",str(exe)],cwd=td,check=True,text=True,stdout=subprocess.PIPE).stdout
  else: out=subprocess.run(["xrun","-sv","-q","-timescale","1ns/1ps","-top","tb",str(HERE/'hierarchical_value_wall.sv'),str(tb)],cwd=td,check=True,text=True,stdout=subprocess.PIPE).stdout
  actual=[l.split()[1:] for l in out.splitlines() if l.startswith('ROW ')];
  if actual!=expected: raise SystemExit(f"{sim}: {actual} != {expected}")
  print(f"{sim}: 2 rows MATCH")
print("ordinary census: exact HierarchicalValueExpression / parsePExpr refusal")
