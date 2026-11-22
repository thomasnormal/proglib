#!/usr/bin/env python3
"""Differential receipt for an edge blocking race through an assign."""
from pathlib import Path
import os
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
SOURCE = HERE / "edge_assign_race_refuse.sv"
EXPECTED = {
    "iverilog": ["x", "x", "x", "0", "0", "0"],
    "xrun": ["x", "x", "x", "1", "1", "0"],
}
TB = '''module tb;
  logic clk, d; wire b;
  edge_assign_race_refuse dut(.clk(clk), .d(d), .b(b));
  initial begin
    clk = 0; d = 0; #1 $display("ROW %b", b);
    d = 1; clk = 1; #1 $display("ROW %b", b);
    clk = 0; #1 $display("ROW %b", b);
    d = 0; clk = 1; #1 $display("ROW %b", b);
    clk = 0; #1 $display("ROW %b", b);
    d = 1; clk = 1; #1 $display("ROW %b", b);
    $finish;
  end
endmodule
'''

for simulator in ("iverilog", "xrun"):
    if simulator == "xrun" and not shutil.which("xrun"):
        continue
    with tempfile.TemporaryDirectory(prefix="sv-edge-assign-race-", dir=os.environ.get("SV_RUN_DIR")) as td:
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
