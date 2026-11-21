#!/usr/bin/env python3
"""Differential receipt for the §4.7 multi-write blocking preemption wall."""
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCE = HERE / "preempt_block_refuse.sv"
EXPECTED = ["0 0 0", "1 1 1", "0 0 0", "1 1 1"]
TB = r'''module tb;
  logic a, b;
  wire q, r, z;
  preempt_block_refuse dut(.a(a), .b(b), .q(q), .r(r), .z(z));
  initial begin
    a = 1'b0; b = 1'b0; #1 $display("ROW %b %b %b", q, r, z);
    a = 1'b1; b = 1'b0; #1 $display("ROW %b %b %b", q, r, z);
    a = 1'b0; b = 1'b1; #1 $display("ROW %b %b %b", q, r, z);
    a = 1'b1; b = 1'b1; #1 $display("ROW %b %b %b", q, r, z);
    $finish;
  end
endmodule'''


def run(cmd, cwd):
    p = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=180)
    if p.returncode:
        raise RuntimeError(p.stdout)
    return p.stdout


def rows(output):
    return [" ".join(line.split()[1:]) for line in output.splitlines()
            if line.startswith("ROW ")]


def main():
    run(["lake", "env", "lean", str(HERE / "agree.lean")], ROOT)
    with tempfile.TemporaryDirectory(prefix="sv-preemptive-", dir=ROOT) as work:
        work = Path(work)
        tb = work / "tb.sv"
        tb.write_text(TB)
        exe = work / "sim"
        run(["iverilog", "-g2012", "-s", "tb", "-o", str(exe),
             str(SOURCE), str(tb)], work)
        actual = rows(run(["vvp", str(exe)], work))
        if actual != EXPECTED:
            raise RuntimeError(f"Icarus rows {actual} != {EXPECTED}")
        print("Icarus Verilog 13.0: four rows MATCH 0/1/0/1")
        if shutil.which("xrun"):
            actual = rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                               "-top", "tb", str(SOURCE), str(tb)], work))
            if actual != EXPECTED:
                raise RuntimeError(f"Xcelium rows {actual} != {EXPECTED}")
            print("Xcelium Verilog 24.03-s004: four rows MATCH 0/1/0/1")
        else:
            print("Xcelium Verilog 24.03-s004: no result, xrun unavailable")


if __name__ == "__main__":
    main()
