#!/usr/bin/env python3
"""Differential receipt for enum references in package aggregate defaults."""
import os
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCE = HERE / "enum_aggregate_default.sv"
TB = """module tb;
  logic x; wire y;
  enum_aggregate_default dut(.x(x), .y(y));
  task row(input logic v); begin x=v; #1 $display(\"ROW %b\", y); end endtask
  initial begin row(1'b0); row(1'b1); row(1'bx); row(1'bz); $finish; end
endmodule
"""
EXPECTED = ["ROW 0", "ROW 1", "ROW x", "ROW z"]


def main():
    subprocess.run(["lake", "env", "lean", str(HERE / "agree.lean")],
                   cwd=ROOT, check=True, timeout=180)
    scratch = os.environ.get("TMPDIR")
    if not scratch:
        raise RuntimeError("TMPDIR must point to lane scratch")
    for sim in ("iverilog", "xrun"):
        with tempfile.TemporaryDirectory(prefix=f"sv-enum-aggregate-{sim}-",
                                          dir=scratch) as work:
            work = Path(work)
            tb = work / "tb.sv"
            tb.write_text(TB)
            if sim == "iverilog":
                exe = work / "sim"
                proc = subprocess.run(
                    ["iverilog", "-g2012", "-s", "tb", "-o", str(exe),
                     str(tb), str(SOURCE)], cwd=work, text=True,
                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                    check=False, timeout=180)
                if proc.returncode == 0:
                    raise RuntimeError("iverilog unexpectedly accepted the faithful assignment pattern")
                print("iverilog: EXPECTED source syntax refusal")
                continue
            proc = subprocess.run(
                ["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "tb",
                 str(SOURCE), str(tb)], cwd=work, text=True,
                stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                check=True, timeout=180)
            rows = [line for line in proc.stdout.splitlines() if line.startswith("ROW ")]
            if rows != EXPECTED:
                raise RuntimeError(f"xrun rows {rows!r} != {EXPECTED!r}")
            print("xrun: 4 source rows MATCH")


if __name__ == "__main__":
    main()
