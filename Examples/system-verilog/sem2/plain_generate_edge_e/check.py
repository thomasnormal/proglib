#!/usr/bin/env python3
"""Differential receipt for a plain event process inside a generate loop."""
from pathlib import Path
import json
import os
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
TMP = Path(os.environ.get("TMPDIR", "build-tmp"))
TMP.mkdir(parents=True, exist_ok=True)
SRC = HERE / "plain_generate_edge_e.sv"
ENV = HERE / "plain_generate_edge_e.sv.json"

# Slang is the only parser.  Re-extraction must reproduce the checked-in
# symbolic envelope, including the retained AlwaysEvent body and GenerateFor.
with tempfile.TemporaryDirectory(dir=TMP, prefix="sv-r14-extract-") as td:
    out = Path(td) / ENV.name
    subprocess.run([
        "python3", "extractors/sv/extract.py", "--top", "plain_generate_edge_e",
        "--retain-loops", "--retain-proc-rewrites", "-o", str(out), str(SRC)
    ], cwd=ROOT, check=True, stdout=subprocess.PIPE, text=True)
    if out.read_bytes() != ENV.read_bytes():
        raise SystemExit("checked-in envelope differs from approved Slang extraction")

census = subprocess.run(
    ["python3", "harness/sv/refusal_census.py", "ordinary", str(ENV)],
    cwd=ROOT, check=True, text=True, stdout=subprocess.PIPE,
).stdout.splitlines()
summary = json.loads(census[-1])
if summary.get("refusals") != 0:
    raise SystemExit(f"ordinary loader refused generate-loop plain always: {census}")

TB = r'''module tb;
  logic clk; logic [1:0] d; wire [1:0] q;
  plain_generate_edge_e dut(.clk(clk), .d(d), .q(q));
  task row(input logic c, input logic [1:0] x);
    begin clk = c; d = x; #1 $display("ROW %b %b", d, q); end
  endtask
  initial begin
    row(1'b0, 2'b00);
    row(1'b1, 2'b01);
    row(1'b0, 2'b10);
    row(1'b1, 2'b10);
    row(1'bx, 2'bxx);
    row(1'b1, 2'bzz);
    row(1'b0, 2'b11);
    row(1'b1, 2'b11);
    $finish;
  end
endmodule
'''
expected = [("00", "xx"), ("01", "10"), ("10", "10"), ("10", "01"),
            ("xx", "01"), ("zz", "zz"), ("11", "zz"), ("11", "11")]
for sim in ("iverilog", "xrun"):
    with tempfile.TemporaryDirectory(dir=TMP, prefix="sv-r14-sim-") as td:
        td = Path(td)
        tb = td / "tb.sv"
        tb.write_text(TB)
        if sim == "iverilog":
            exe = td / "sim"
            subprocess.run(["iverilog", "-g2012", "-s", "tb", "-o", str(exe), str(SRC), str(tb)], cwd=td, check=True)
            run = subprocess.run(["vvp", str(exe)], cwd=td, check=True, text=True, stdout=subprocess.PIPE)
        else:
            run = subprocess.run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "tb", str(SRC), str(tb)], cwd=td, check=True, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        actual = [tuple(line.split()[1:]) for line in run.stdout.splitlines() if line.startswith("ROW ")]
        if actual != expected:
            raise SystemExit(f"{sim}: {actual} != {expected}")
        print(f"{sim}: 8 rows MATCH")
