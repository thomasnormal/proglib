#!/usr/bin/env python3
from pathlib import Path
import json, subprocess, tempfile
HERE=Path(__file__).resolve().parent; ROOT=HERE.parents[3]; ENV=HERE/'inout_wall.sv.json'
env=json.loads(ENV.read_text())
mods=env["design"]["modules"]
top=next(m for m in mods if m["name"] == "inout_repro")
leaf=next(m for m in mods if m["name"] == "inout_leaf")
if [p.get("dir") for p in top["ports"]] != ["in", "inout", "out"]:
 raise SystemExit("top inout direction was not retained")
if [p.get("dir") for p in leaf["ports"]] != ["inout", "in", "out"]:
 raise SystemExit("leaf inout direction was not retained")
conn=top["generates"][0]["ports"][0]
if conn.get("kind") != "PortConn" or conn.get("dir") != "inout" or conn.get("expr",{}).get("kind") != "Ident":
 raise SystemExit(f"inout port connection was not retained: {conn}")
TB='''module tb; tri pad; logic drive, ext_en, ext; wire seen; inout_repro dut(.drive(drive),.pad(pad),.seen(seen)); assign pad = ext_en ? ext : 1'bz; initial begin drive=0;ext_en=0;ext=0;#1 $display("ROW %b %b",pad,seen); drive=1;#1 $display("ROW %b %b",pad,seen); drive=0;ext_en=1;ext=0;#1 $display("ROW %b %b",pad,seen); ext=1;#1 $display("ROW %b %b",pad,seen); ext=0;drive=1;#1 $display("ROW %b %b",pad,seen); ext_en=0;#1 $display("ROW %b %b",pad,seen); $finish; end endmodule'''
expected=[["z","z"],["1","1"],["0","0"],["1","1"],["x","x"],["1","1"]]
for sim in ("iverilog","xrun"):
 with tempfile.TemporaryDirectory(prefix="sv-inout-") as td:
  tb=Path(td)/"tb.sv";tb.write_text(TB)
  if sim=="iverilog":
   exe=Path(td)/"sim";subprocess.run(["iverilog","-g2012","-s","tb","-o",str(exe),str(HERE/'inout_wall.sv'),str(tb)],cwd=td,check=True);out=subprocess.run(["vvp",str(exe)],cwd=td,check=True,text=True,stdout=subprocess.PIPE).stdout
  else: out=subprocess.run(["xrun","-sv","-q","-timescale","1ns/1ps","-top","tb",str(HERE/'inout_wall.sv'),str(tb)],cwd=td,check=True,text=True,stdout=subprocess.PIPE).stdout
  actual=[l.split()[1:] for l in out.splitlines() if l.startswith('ROW ')];
  if actual!=expected: raise SystemExit(f"{sim}: {actual} != {expected}")
  print(f"{sim}: 6 rows MATCH")
print("ordinary census: exact inout/resolution boundaries")
