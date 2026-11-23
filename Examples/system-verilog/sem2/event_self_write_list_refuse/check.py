#!/usr/bin/env python3
"""Differential receipts for explicit event-list blocking self-writes."""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
CASES = {
    "list": (HERE.parent / "event_self_write_list_refuse" / "event_self_write_list_refuse.sv",
             "event_self_write_list",
             "logic a; wire t,y;",
             "event_self_write_list dut(.a(a),.t(t),.y(y));",
             "a=0; #1 $display(\"ROW %b %b\",t,y); a=1; #1 $display(\"ROW %b %b\",t,y); a=0; #1 $display(\"ROW %b %b\",t,y); a=1; #1 $display(\"ROW %b %b\",t,y); a=0; #1 $display(\"ROW %b %b\",t,y);",
             ["0 x", "1 0", "0 1", "1 0", "0 1"]),
    "latch": (HERE.parent / "event_self_write_latch_refuse" / "event_self_write_latch_refuse.sv",
              "event_self_write_latch",
              "logic en,a; wire t,y;",
              "event_self_write_latch dut(.en(en),.a(a),.t(t),.y(y));",
              "en=0; a=0; #1 $display(\"ROW %b %b\",t,y); en=1; a=1; #1 $display(\"ROW %b %b\",t,y); en=0; a=0; #1 $display(\"ROW %b %b\",t,y); en=1; a=0; #1 $display(\"ROW %b %b\",t,y); en=0; a=1; #1 $display(\"ROW %b %b\",t,y);",
              ["x x", "1 x", "1 x", "0 1", "0 1"]),
}
for kind, (source, module, decls, inst, body, expected) in CASES.items():
    tb_text = f'''module tb; {decls}
  {inst}
  initial begin {body} $finish; end
endmodule
'''
    for simulator in ("iverilog", "xrun"):
        if simulator == "xrun" and not shutil.which("xrun"):
            continue
        with tempfile.TemporaryDirectory(prefix="sv-event-self-write-", dir=os.environ.get("SV_RUN_DIR")) as td:
            td = Path(td); tb = td / "tb.sv"; tb.write_text(tb_text)
            if simulator == "iverilog":
                exe = td / "sim"
                subprocess.run(["iverilog", "-g2012", "-s", "tb", "-o", str(exe), str(source), str(tb)], cwd=td, check=True)
                output = subprocess.check_output(["vvp", str(exe)], cwd=td, text=True)
            else:
                output = subprocess.check_output(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "tb", str(source), str(tb)], cwd=td, text=True, stderr=subprocess.STDOUT)
        rows = [" ".join(line.split()[1:]) for line in output.splitlines() if line.startswith("ROW ")]
        if rows != expected: raise SystemExit(f"{kind} {simulator}: {rows} != {expected}")
        print(f"{kind} {simulator}: {len(rows)} rows MATCH")
