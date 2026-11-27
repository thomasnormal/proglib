#!/usr/bin/env python3
"""Differential rows for a package unpacked-array constant-function read."""
from pathlib import Path
import os
import signal
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = ["00000111", "00000110", "xxxxxxxx", "xxxxxxxx"]


def run(args, cwd=ROOT):
    proc = subprocess.Popen(args, cwd=cwd, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, start_new_session=True)
    try:
        out, err = proc.communicate(timeout=240)
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        raise RuntimeError(f"{args[0]} timed out")
    if proc.returncode:
        raise RuntimeError(f"{args[0]} exited {proc.returncode}: {err}")
    return out


def testbench():
    return '''module x2_pkg_array_tb;
  logic [7:0] i;
  wire [7:0] o;
  leaf dut(.i(i), .o(o));
  initial begin
    i = 8'b00000000; #1 $display("ROW %b", o);
    i = 8'b11111111; #1 $display("ROW %b", o);
    i = 8'bxxxxxxxx; #1 $display("ROW %b", o);
    i = 8'bzzzzzzzz; #1 $display("ROW %b", o);
    $finish;
  end
endmodule
'''


def rows(out):
    return [line.split()[1] for line in out.splitlines() if line.startswith("ROW ")]


def main():
    source = HERE / "x2_pkg_array.sv"
    with tempfile.TemporaryDirectory(prefix="sv-x2-") as work:
        work = Path(work)
        tb = work / "tb.sv"
        tb.write_text(testbench())
        exe = work / "sim"
        iverilog = subprocess.run(
            ["iverilog", "-g2012", "-s", "x2_pkg_array_tb", "-o", str(exe),
             str(source), str(tb)], cwd=work, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        if iverilog.returncode == 0:
            actual = rows(run(["vvp", str(exe)], work))
            if actual != EXPECTED:
                raise RuntimeError(f"Icarus Verilog 13.0: {actual} != {EXPECTED}")
            print("Icarus Verilog 13.0: 4 rows MATCH")
        elif "unpacked array parameters are not supported" in iverilog.stderr:
            print("Icarus Verilog 13.0: parser refusal (unpacked array parameters); no oracle result claimed")
        else:
            raise RuntimeError(f"Icarus Verilog 13.0 exited {iverilog.returncode}: {iverilog.stderr}")
        if shutil.which("xrun"):
            actual = rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                               "-top", "x2_pkg_array_tb", str(source), str(tb)], work))
            if actual != EXPECTED:
                raise RuntimeError(f"Xcelium 26.09-s001: {actual} != {EXPECTED}")
            print("Xcelium 26.09-s001: 4 rows MATCH")


if __name__ == "__main__":
    main()
