#!/usr/bin/env python3
"""Check generated event-control expansion against both pinned simulators."""
from pathlib import Path
import json
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
ENV = HERE / "event_generated_wall.sv.json"
SOURCE = HERE / "event_generated_wall.sv"

rows = [json.loads(line) for line in subprocess.run(
    ["python3", "harness/sv/refusal_census.py", "ordinary", str(ENV)],
    cwd=ROOT, check=True, text=True, stdout=subprocess.PIPE).stdout.splitlines()]
if rows != [{"refusals": 0, "stage": "summary"}]:
    raise SystemExit(f"unexpected ordinary census: {rows}")

tb_source = """module tb;
  logic clk, d, q;
  event_generated_repro dut(.clk(clk), .d(d), .q(q));
  initial begin
    clk = 1'b0; d = 1'b0; #1 $display("ROW %b", q);
    d = 1'b1; clk = 1'b1; #1 $display("ROW %b", q);
    d = 1'b0; clk = 1'b0; #1 $display("ROW %b", q);
    clk = 1'b1; #1 $display("ROW %b", q);
    $finish;
  end
endmodule
"""
expected = [["x"], ["1"], ["1"], ["0"]]
for simulator in ("iverilog", "xrun"):
    with tempfile.TemporaryDirectory(prefix="sv-event-generated-") as directory:
        directory = Path(directory)
        tb = directory / "tb.sv"
        tb.write_text(tb_source)
        if simulator == "iverilog":
            executable = directory / "sim"
            subprocess.run(
                ["iverilog", "-g2012", "-s", "tb", "-o", str(executable),
                 str(SOURCE), str(tb)], cwd=directory, check=True)
            output = subprocess.run(
                ["vvp", str(executable)], cwd=directory, check=True,
                text=True, stdout=subprocess.PIPE).stdout
        else:
            output = subprocess.run(
                ["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "tb",
                 str(SOURCE), str(tb)], cwd=directory, check=True,
                text=True, stdout=subprocess.PIPE).stdout
        actual = [line.split()[1:] for line in output.splitlines()
                  if line.startswith("ROW ")]
        if actual != expected:
            raise SystemExit(f"{simulator}: {actual} != {expected}")
        print(f"{simulator}: 4 rows MATCH")
print("ordinary census: generated AlwaysEvent retained and admitted by canonical E")
