#!/usr/bin/env python3
"""Differential receipt for selected-assign and always_comb edge races."""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile
HERE = Path(__file__).resolve().parent
SOURCE = HERE / "edge_driver_closure_race_refuse.sv"
TB = '''module tb;
  logic clk, d; wire b_assign, b_comb;
  edge_driver_closure_race_refuse dut(.clk(clk), .d(d), .b_assign(b_assign), .b_comb(b_comb));
  initial begin
    clk=0; d=0; #1 $display("ROW %b%b", b_assign, b_comb);
    d=1; clk=1; #1 $display("ROW %b%b", b_assign, b_comb);
    clk=0; #1 $display("ROW %b%b", b_assign, b_comb);
    d=0; clk=1; #1 $display("ROW %b%b", b_assign, b_comb);
    clk=0; #1 $display("ROW %b%b", b_assign, b_comb);
    d=1; clk=1; #1 $display("ROW %b%b", b_assign, b_comb);
    $finish;
  end
endmodule
'''
EXPECTED = {"iverilog": ["xx", "xx", "xx", "01", "01", "00"], "xrun": ["xx", "xx", "xx", "11", "11", "00"]}
for simulator in ("iverilog", "xrun"):
    if simulator == "xrun" and not shutil.which("xrun"):
        continue
    with tempfile.TemporaryDirectory(prefix="sv-edge-driver-", dir=os.environ.get("SV_RUN_DIR")) as td:
        td = Path(td); tb = td / "tb.sv"; tb.write_text(TB)
        if simulator == "iverilog":
            exe = td / "sim"
            subprocess.run(["iverilog", "-g2012", "-s", "tb", "-o", str(exe), str(SOURCE), str(tb)], cwd=td, check=True)
            output = subprocess.check_output(["vvp", str(exe)], cwd=td, text=True)
        else:
            output = subprocess.check_output(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "tb", str(SOURCE), str(tb)], cwd=td, text=True, stderr=subprocess.STDOUT)
    rows = [line.split()[1] for line in output.splitlines() if line.startswith("ROW ")]
    if rows != EXPECTED[simulator]: raise SystemExit(f"{simulator}: {rows} != {EXPECTED[simulator]}")
    print(f"{simulator}: {len(rows)} rows MATCH")
