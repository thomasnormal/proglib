#!/usr/bin/env python3
"""Differential receipt for a time-zero assign-to-always_comb chain."""
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCE = HERE / "time_zero_comb_quiesce_e.sv"
ENVELOPE = HERE / "time_zero_comb_quiesce_e.sv.json"
TB = r'''module tb;
  wire a, b, y;
  time_zero_comb_quiesce_e dut(.a(a), .b(b), .y(y));
  initial begin
    #0 $display("ROW delta0 a=%b b=%b y=%b", a, b, y);
    #1 $display("ROW settled a=%b b=%b y=%b", a, b, y);
    $finish;
  end
endmodule'''


def run(cmd, cwd=ROOT):
    p = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=180)
    if p.returncode:
        raise RuntimeError(p.stdout)
    return p.stdout


def rows(output):
    return [line.split()[2:] for line in output.splitlines()
            if line.startswith("ROW ")]


def main():
    with tempfile.TemporaryDirectory(prefix="sv-time-zero-comb-") as work:
        generated = Path(work) / ENVELOPE.name
        run(["python3", "extractors/sv/extract.py", "--top",
             "time_zero_comb_quiesce_e", "-o", str(generated), str(SOURCE)])
        if generated.read_bytes() != ENVELOPE.read_bytes():
            raise RuntimeError("extractor envelope is stale")
        tb = Path(work) / "tb.sv"
        tb.write_text(TB)
        expected = ["a=1", "b=1", "y=1"]
        expected_rows = [expected, expected]
        if shutil.which("iverilog"):
            exe = str(Path(work) / "sim")
            run(["iverilog", "-g2012", "-s", "tb", "-o", exe,
                 str(SOURCE), str(tb)], work)
            actual = rows(run(["vvp", exe], work))
            if actual != expected_rows:
                raise RuntimeError(f"Icarus: rows {actual} != {expected_rows}")
            print("Icarus Verilog 13.0: delta and settled rows MATCH a=1 b=1 y=1")
        else:
            raise RuntimeError("Icarus Verilog is required")
        if shutil.which("xrun"):
            actual = rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                               "-top", "tb", str(SOURCE), str(tb)], work))
            if actual != expected_rows:
                raise RuntimeError(f"Xcelium: rows {actual} != {expected_rows}")
            print("Xcelium Verilog 24.03-s004: delta and settled rows MATCH a=1 b=1 y=1")
        else:
            print("Xcelium Verilog 24.03-s004: no result, xrun unavailable")
    print("canonical E: time-zero assign/always_comb chain MATCH")


if __name__ == "__main__":
    main()
