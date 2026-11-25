#!/usr/bin/env python3
from pathlib import Path
import os
import subprocess, tempfile

HERE = Path(__file__).resolve().parent
SOURCE = HERE / "memory_only_quiesce.sv"
XRUN = Path("/opt/cadence/installs/XCELIUM2403/tools/bin/64bit/xrun")
TB = """module tb;
  logic seed; wire q;
  memory_only_quiesce dut(.seed(seed), .q(q));
  initial begin
    seed=0; #1 $display("ROW seed0 q=%b mem=%b%b", q, dut.mem[0], dut.mem[1]);
    seed=1; #1 $display("ROW seed1 q=%b mem=%b%b", q, dut.mem[0], dut.mem[1]);
    $finish;
  end
endmodule
"""
EXPECTED = ["ROW seed0 q=0 mem=00", "ROW seed1 q=0 mem=11"]

scratch_dir = Path(os.environ.get("TMPDIR", "/scratch"))
with tempfile.TemporaryDirectory(prefix="sv-memory-quiesce-",
                                 dir=scratch_dir) as td:
    work = Path(td)
    tb = work / "tb.sv"
    tb.write_text(TB)
    exe = work / "sim"
    subprocess.run(["iverilog", "-g2012", "-s", "tb", "-o", str(exe),
                    str(SOURCE), str(tb)], check=True)
    output = subprocess.check_output(["vvp", str(exe)], text=True)
    rows = [line for line in output.splitlines() if line.startswith("ROW ")]
    if rows != EXPECTED:
        raise SystemExit(f"Icarus Verilog 13.0: {rows} != {EXPECTED}")
    print("Icarus Verilog 13.0: 2 rows MATCH")
    output = subprocess.check_output(
        [str(XRUN), "-sv", "-q", "-timescale", "1ns/1ps", "-top", "tb",
         str(SOURCE), str(tb)], cwd=work, text=True,
        stderr=subprocess.STDOUT)
    rows = [line for line in output.splitlines() if line.startswith("ROW ")]
    if rows != EXPECTED:
        raise SystemExit(f"Xcelium 24.03-s004: {rows} != {EXPECTED}")
    print("Xcelium 24.03-s004: 2 rows MATCH")
