#!/usr/bin/env python3
"""Differential rows for the two always_latch self-read refusal shapes."""
from pathlib import Path
import os
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
CASES = (
    ("latch_self_read_a.sv", "latch_self_read_a", ["x", "x", "x", "x", "x", "0"]),
    ("latch_self_read_b.sv", "latch_self_read_b", ["x", "x", "0", "0", "0", "0"]),
)

TB = '''module tb;
  logic en, a; wire y;
  DUT dut(.en(en), .a(a), .y(y));
  initial begin
    en = 1'b0; a = 1'b0; #1 $display("ROW %b", y);
    en = 1'b1; a = 1'b0; #1 $display("ROW %b", y);
    en = 1'b0; a = 1'b1; #1 $display("ROW %b", y);
    en = 1'bx; a = 1'b0; #1 $display("ROW %b", y);
    en = 1'bz; a = 1'b0; #1 $display("ROW %b", y);
    en = 1'b1; a = 1'b1; #1 $display("ROW %b", y);
    $finish;
  end
endmodule
'''


def run_case(source, top, expected, simulator):
    run_dir = os.environ.get("SV_RUN_DIR")
    if run_dir is None:
        raise SystemExit("SV_RUN_DIR must point to the lane scratch directory")
    with tempfile.TemporaryDirectory(prefix="sv-latch-self-read-", dir=run_dir) as td:
        td = Path(td)
        tb = td / "tb.sv"
        tb.write_text(TB.replace("DUT", top))
        if simulator == "iverilog":
            exe = td / "sim"
            subprocess.run(["iverilog", "-g2012", "-s", "tb", "-o", str(exe), str(source), str(tb)],
                           cwd=td, check=True)
            out = subprocess.run(["vvp", str(exe)], cwd=td, check=True,
                                 text=True, stdout=subprocess.PIPE).stdout
        else:
            out = subprocess.run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "tb",
                                  str(source), str(tb)], cwd=td, check=True,
                                 text=True, stdout=subprocess.PIPE).stdout
        rows = [line.split()[1] for line in out.splitlines() if line.startswith("ROW ")]
        if rows != expected:
            raise SystemExit(f"{top}/{simulator}: {rows} != {expected}")
        print(f"{top}/{simulator}: {len(rows)} rows MATCH")


for simulator in ("iverilog", "xrun"):
    if simulator == "xrun" and not subprocess.run(["sh", "-c", "command -v xrun"], check=False).returncode == 0:
        continue
    for source_name, top, expected in CASES:
        run_case(HERE / source_name, top, expected, simulator)
