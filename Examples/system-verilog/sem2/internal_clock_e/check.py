#!/usr/bin/env python3
from pathlib import Path
import json, subprocess, tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
ENV = HERE / "internal_clock_e.sv.json"
rows = [json.loads(x) for x in subprocess.run(["python3","harness/sv/refusal_census.py","ordinary",str(ENV)], cwd=ROOT, check=True, text=True, stdout=subprocess.PIPE).stdout.splitlines()]
if not any(r.get("construct") == "Clock:source" for r in rows): raise SystemExit(f"missing Clock:source: {rows}")
TB = '''module tb; logic enable,data,result; internal_clock_repro dut(.enable(enable),.data(data),.result(result)); initial begin enable=0;data=0;#1 $display("ROW %b",result); enable=1;data=1;#1 $display("ROW %b",result); enable=1'bx;data=0;#1 $display("ROW %b",result); enable=1'bz;data=1;#1 $display("ROW %b",result); enable=1;data=0;#1 $display("ROW %b",result); $finish; end endmodule'''
expected = [["x"],["1"],["1"],["1"],["0"]]
for sim in ("iverilog", "xrun"):
  with tempfile.TemporaryDirectory(prefix="sv-intclk-") as td:
    tb = Path(td)/"tb.sv"; tb.write_text(TB)
    if sim == "iverilog":
      exe = Path(td)/"sim"; subprocess.run(["iverilog","-g2012","-s","tb","-o",str(exe),str(HERE/"internal_clock_e.sv"),str(tb)], cwd=td, check=True); out=subprocess.run(["vvp",str(exe)],cwd=td,check=True,text=True,stdout=subprocess.PIPE).stdout
    else: out=subprocess.run(["xrun","-sv","-q","-timescale","1ns/1ps","-top","tb",str(HERE/"internal_clock_e.sv"),str(tb)],cwd=td,check=True,text=True,stdout=subprocess.PIPE).stdout
    actual=[line.split()[1:] for line in out.splitlines() if line.startswith("ROW ")]
    if actual != expected: raise SystemExit(f"{sim}: {actual} != {expected}")
    print(f"{sim}: 5 rows MATCH")
print("ordinary loader: exact Clock:source refusal; canonical E receipt is direct instantiateE2")
