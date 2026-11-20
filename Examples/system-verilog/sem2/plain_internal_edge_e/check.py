#!/usr/bin/env python3
from pathlib import Path
import subprocess, tempfile, json
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
rows = [json.loads(x) for x in subprocess.run(["python3", "harness/sv/refusal_census.py", "ordinary", str(HERE/"plain_internal_edge_e.sv.json")], cwd=ROOT, check=True, text=True, stdout=subprocess.PIPE).stdout.splitlines()]
if not any(r.get("construct") == "Clock:source" for r in rows): raise SystemExit(f"missing Clock:source refusal: {rows}")
TB = '''module tb; logic clk,d,g_plain,q_plain,g_ff,q_ff; plain_internal_edge_e dut(.*); initial begin clk=0; d=0; #1 $display("ROW %b%b",q_plain,q_ff); d=1; clk=1; #1 $display("ROW %b%b",q_plain,q_ff); clk=0; #1 $display("ROW %b%b",q_plain,q_ff); d=1'bx; clk=1'bx; #1 $display("ROW %b%b",q_plain,q_ff); d=1'bz; clk=1'bz; #1 $display("ROW %b%b",q_plain,q_ff); d=1'bx; clk=1; #1 $display("ROW %b%b",q_plain,q_ff); $finish; end endmodule'''
expected = [["xx"],["11"],["11"],["11"],["11"],["11"]]
for sim in ("iverilog", "xrun"):
  with tempfile.TemporaryDirectory(prefix="sv-r13-") as td:
    tb = Path(td)/"tb.sv"; tb.write_text(TB)
    if sim == "iverilog":
      exe = Path(td)/"sim"; subprocess.run(["iverilog","-g2012","-s","tb","-o",str(exe),str(HERE/"plain_internal_edge_e.sv"),str(tb)], cwd=td, check=True); out=subprocess.run(["vvp",str(exe)],cwd=td,check=True,text=True,stdout=subprocess.PIPE).stdout
    else: out=subprocess.run(["xrun","-sv","-q","-timescale","1ns/1ps","-top","tb",str(HERE/"plain_internal_edge_e.sv"),str(tb)],cwd=td,check=True,text=True,stdout=subprocess.PIPE).stdout
    actual=[line.split()[1:] for line in out.splitlines() if line.startswith("ROW ")]
    if actual != expected: raise SystemExit(f"{sim}: {actual} != {expected}")
    print(f"{sim}: 6 rows MATCH")
