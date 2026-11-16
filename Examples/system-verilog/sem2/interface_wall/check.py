#!/usr/bin/env python3
from pathlib import Path
import json, subprocess, tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
ENV = HERE / "interface_wall.sv.json"
text = subprocess.run(["python3","harness/sv/refusal_census.py","ordinary",str(ENV)], cwd=ROOT, check=True, text=True, stdout=subprocess.PIPE).stdout
rows = [json.loads(x) for x in text.splitlines()]
want = {
    ("InstanceSymbol:interface", "GenItem.expand"),
    ("PortConnection:InterfacePortSymbol", "parsePConn"),
    ("Instantiation:E:unsupported", "PDesign.instantiateE2"),
    ("AssignmentExpression:target", "parsePProcess"),
}
seen = {(r.get("construct"), r.get("function")) for r in rows}
if not want.issubset(seen): raise SystemExit(f"missing exact interface walls: {rows}")
tb = Path(tempfile.mkdtemp(prefix="sv-interface-") ) / "tb.sv"
tb.write_text('''module tb; logic clock,value,result; interface_repro dut(.clock(clock),.value(value),.result(result)); initial begin clock=0; value=0; #1 $display("ROW %b",result); value=1; #1 $display("ROW %b",result); value=1'bx; #1 $display("ROW %b",result); value=1'bz; #1 $display("ROW %b",result); $finish; end endmodule''')
out = subprocess.run(["xrun","-sv","-q","-timescale","1ns/1ps","-top","tb",str(HERE / "interface_wall.sv"),str(tb)], cwd=tb.parent, check=True, text=True, stdout=subprocess.PIPE).stdout
actual = [line.split()[1:] for line in out.splitlines() if line.startswith("ROW ")]
if actual != [["0"],["1"],["x"],["z"]]: raise SystemExit(f"xrun: {actual}")
print("ordinary census: exact interface instance/port boundaries")
print("xrun: 4 x/z rows MATCH")
print("iverilog: no oracle claimed (interface port syntax rejected)")
