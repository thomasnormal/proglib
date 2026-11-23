#!/usr/bin/env python3
"""Differential receipt for an edge blocking race through two child ports."""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
SOURCE = HERE / "edge_two_level_child_port_race_refuse.sv"
EXPECTED = {
    "iverilog": ["x", "1", "1", "1", "1", "1"],
    "xrun": ["x", "x", "x", "1", "1", "0"],
}
TB = '''module tb;
  logic clk, d; wire q;
  edge_two_level_child_port_race dut(.clk(clk), .d(d), .q(q));
  initial begin
    clk = 0; d = 0; #1 $display("ROW %b", q);
    d = 1; clk = 1; #1 $display("ROW %b", q);
    clk = 0; #1 $display("ROW %b", q);
    d = 0; clk = 1; #1 $display("ROW %b", q);
    clk = 0; #1 $display("ROW %b", q);
    d = 1; clk = 1; #1 $display("ROW %b", q);
    $finish;
  end
endmodule
'''

for simulator in ("iverilog", "xrun"):
    if simulator == "xrun" and not shutil.which("xrun"):
        continue
    with tempfile.TemporaryDirectory(prefix="sv-edge-two-level-", dir=os.environ.get("SV_RUN_DIR")) as td:
        td = Path(td)
        tb = td / "tb.sv"
        tb.write_text(TB)
        if simulator == "iverilog":
            exe = td / "sim"
            subprocess.run(["iverilog", "-g2012", "-s", "tb", "-o", str(exe), str(SOURCE), str(tb)],
                           cwd=td, check=True)
            output = subprocess.check_output(["vvp", str(exe)], cwd=td, text=True)
        else:
            output = subprocess.check_output(
                ["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "tb", str(SOURCE), str(tb)],
                cwd=td, text=True, stderr=subprocess.STDOUT)
    rows = [line.split()[1] for line in output.splitlines() if line.startswith("ROW ")]
    if rows != EXPECTED[simulator]:
        raise SystemExit(f"{simulator}: {rows} != {EXPECTED[simulator]}")
    print(f"{simulator}: {len(rows)} rows MATCH")
