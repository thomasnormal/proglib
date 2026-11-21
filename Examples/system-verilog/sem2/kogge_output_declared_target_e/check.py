#!/usr/bin/env python3
"""Differential receipt for packed output bit-select continuous targets."""
from pathlib import Path
import json
import os
import subprocess
import tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
TMP = Path(os.environ.get("TMPDIR", "/scratch/ls-sv/tmp"))
TMP.mkdir(parents=True, exist_ok=True)
SRC = HERE / "kogge_output_declared_target_e.sv"
ENV = HERE / "kogge_output_declared_target_e.sv.json"
with tempfile.TemporaryDirectory(dir=TMP, prefix="sv-packed-target-extract-") as td:
    out = Path(td) / ENV.name
    subprocess.run(["python3", "extractors/sv/extract.py", "--top", "kogge_output_declared_target_e", "-o", str(out), str(SRC)], cwd=ROOT, check=True, stdout=subprocess.PIPE, text=True)
    if out.read_bytes() != ENV.read_bytes():
        raise SystemExit("checked-in envelope differs from approved Slang extraction")
census = subprocess.run(["python3", "harness/sv/refusal_census.py", "ordinary", str(ENV)], cwd=ROOT, check=True, text=True, stdout=subprocess.PIPE).stdout.splitlines()
if json.loads(census[-1]).get("refusals") != 0:
    raise SystemExit("ordinary loader refused packed output target")
TB = r'''module tb;
  logic [3:0] a; wire [3:0] o_sum;
  kogge_output_declared_target_e dut(.a(a), .o_sum(o_sum));
  task row(input logic [3:0] x); begin a = x; #1 $display("ROW %b %b", a, o_sum); end endtask
  initial begin row(4'b0000); row(4'b0011); row(4'bxxxx); row(4'bzzzz); $finish; end
endmodule
'''
expected = [("0000", "0000"), ("0011", "0011"), ("xxxx", "xxxx"), ("zzzz", "zzzz")]
for sim in ("iverilog", "xrun"):
    with tempfile.TemporaryDirectory(dir=TMP, prefix="sv-packed-target-sim-") as td:
        td = Path(td); tb = td / "tb.sv"; tb.write_text(TB)
        if sim == "iverilog":
            exe = td / "sim"
            subprocess.run(["iverilog", "-g2012", "-s", "tb", "-o", str(exe), str(SRC), str(tb)], cwd=td, check=True)
            run = subprocess.run(["vvp", str(exe)], cwd=td, check=True, text=True, stdout=subprocess.PIPE)
        else:
            run = subprocess.run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "tb", str(SRC), str(tb)], cwd=td, check=True, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        actual = [tuple(line.split()[1:]) for line in run.stdout.splitlines() if line.startswith("ROW ")]
        if actual != expected:
            raise SystemExit(f"{sim}: {actual} != {expected}")
        print(f"{sim}: 4 rows MATCH")
