#!/usr/bin/env python3
"""Differential receipt for named generate-scope storage identity."""
from pathlib import Path
import json
import os
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
TMP = Path(os.environ.get("TMPDIR", "/scratch/ls-sv/tmp"))
TMP.mkdir(parents=True, exist_ok=True)
SRC = HERE / "duplicate_active_scope_e.sv"
ENV = HERE / "duplicate_active_scope_e.sv.json"
with tempfile.TemporaryDirectory(dir=TMP, prefix="sv-duplicate-scope-extract-") as td:
    out = Path(td) / ENV.name
    subprocess.run([
        "python3", "extractors/sv/extract.py", "--top",
        "duplicate_active_scope_e", "-o", str(out), str(SRC)
    ], cwd=ROOT, check=True, stdout=subprocess.PIPE, text=True)
    if out.read_bytes() != ENV.read_bytes():
        raise SystemExit("checked-in envelope differs from approved Slang extraction")
census = subprocess.run([
    "python3", "harness/sv/refusal_census.py", "ordinary", str(ENV)
], cwd=ROOT, check=True, text=True, stdout=subprocess.PIPE).stdout.splitlines()
if json.loads(census[-1]).get("refusals") != 0:
    raise SystemExit("ordinary loader refused duplicate active generated scopes")
TB = r'''module tb;
  logic [1:0] x; wire [1:0] y;
  duplicate_active_scope_e dut(.x(x), .y(y));
  task row(input logic [1:0] v); begin x=v; #1 $display("ROW %b %b", x, y); end endtask
  initial begin row(2'b00); row(2'b11); row(2'bxx); row(2'bzz); $finish; end
endmodule
'''
expected = [("00", "00"), ("11", "11"), ("xx", "xx"), ("zz", "zz")]
def rows(output):
    return [tuple(line.split()[1:]) for line in output.splitlines()
            if line.startswith("ROW ")]
for sim in ("iverilog", "xrun"):
    if sim == "xrun" and not shutil.which("xrun"):
        print("xrun: unavailable")
        continue
    with tempfile.TemporaryDirectory(dir=TMP, prefix="sv-duplicate-scope-sim-") as td:
        td = Path(td)
        tb = td / "tb.sv"
        tb.write_text(TB)
        if sim == "iverilog":
            exe = td / "sim"
            subprocess.run([
                "iverilog", "-g2012", "-s", "tb", "-o", str(exe),
                str(SRC), str(tb)
            ], cwd=td, check=True)
            run = subprocess.run(["vvp", str(exe)], cwd=td, check=True,
                                 text=True, stdout=subprocess.PIPE)
        else:
            run = subprocess.run([
                "xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top",
                "tb", str(SRC), str(tb)
            ], cwd=td, check=True, text=True,
               stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        actual = rows(run.stdout)
        if actual != expected:
            raise SystemExit(f"{sim}: {actual} != {expected}")
        print(f"{sim}: {len(actual)} rows MATCH")
