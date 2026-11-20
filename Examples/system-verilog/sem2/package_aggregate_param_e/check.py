#!/usr/bin/env python3
"""Differential receipt for a fixed unpacked package aggregate parameter."""
from pathlib import Path
import os
import shutil, subprocess, tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCE = HERE / "package_aggregate_param_e.sv"
EXPECTED = ["000000", "101010", "010101", "111111", "xxxxxx"]
TB = """module tb;
  logic [1:0] i; wire [5:0] y;
  package_aggregate_param_e dut(.i(i), .y(y));
  initial begin
    i=2'b00; #1 $display("ROW %b", y);
    i=2'b01; #1 $display("ROW %b", y);
    i=2'b10; #1 $display("ROW %b", y);
    i=2'b11; #1 $display("ROW %b", y);
    i=2'bxx; #1 $display("ROW %b", y); $finish;
  end
endmodule
"""
def run(args, cwd=ROOT):
    return subprocess.run(args, cwd=cwd, check=True, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT).stdout
def main():
    with tempfile.NamedTemporaryFile(suffix=".sv") as tb:
        Path(tb.name).write_text(TB)
        if shutil.which("iverilog"):
            with tempfile.TemporaryDirectory(prefix="sv-package-aggregate-iverilog-", dir=os.environ.get("TMPDIR")) as work:
                exe = str(Path(work) / "sim")
                p = subprocess.run(["iverilog", "-g2012", "-s", "tb", "-o", exe,
                                    str(SOURCE), tb.name], cwd=ROOT, text=True,
                                   stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            if p.returncode == 0:
                raise RuntimeError("Icarus Verilog 13.0 unexpectedly accepted the faithful aggregate syntax")
            print("Icarus Verilog 13.0: faithful unpacked aggregate parameter syntax refusal")
        if shutil.which("xrun"):
            with tempfile.TemporaryDirectory(prefix="sv-package-aggregate-xcelium-", dir=os.environ.get("TMPDIR")) as work:
                out = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ns", "-top", "tb", str(SOURCE), tb.name], Path(work))
            rows = [line.split()[1] for line in out.splitlines() if line.startswith("ROW ")]
            if rows != EXPECTED:
                raise RuntimeError(f"Xcelium 24.03-s004: {rows} != {EXPECTED}")
            print("Xcelium 24.03-s004: 5 source rows MATCH")
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    print("canonical E: 5 rows MATCH fixed unpacked package aggregate")
if __name__ == "__main__":
    main()
