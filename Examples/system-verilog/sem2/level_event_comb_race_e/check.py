#!/usr/bin/env python3
"""Differential receipt for the level-event/reactive activation wall."""
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
SOURCE = HERE / "level_event_comb_race_e.sv"
EXPECTED = ["x", "0", "0", "0", "0"]
TB = r'''`timescale 1ns/1ps
module tb;
  logic en, a, b;
  logic y;
  level_event_comb_race_e dut(.en(en), .a(a), .b(b), .y(y));
  initial begin
    #10 {en, a, b} = {1'b1, 1'b0, 1'b0};
    #5 $display("ROW %b", dut.y);
    #5 {en, a, b} = {1'b1, 1'b1, 1'b0};
    #5 $display("ROW %b", dut.y);
    #5 {en, a, b} = {1'b1, 1'b0, 1'b0};
    #5 $display("ROW %b", dut.y);
    #5 {en, a, b} = {1'b1, 1'b1, 1'b0};
    #5 $display("ROW %b", dut.y);
    #5 {en, a, b} = {1'b0, 1'b1, 1'b0};
    #5 $display("ROW %b", dut.y);
    #10 $finish;
  end
endmodule'''


def rows(output):
    return [line.split()[1] for line in output.splitlines() if line.startswith("ROW ")]


def run(cmd, cwd):
    return subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, check=True, timeout=180).stdout


def main():
    with tempfile.TemporaryDirectory(prefix="sv-level-event-race-") as td:
        work = Path(td)
        tb = work / "tb.sv"
        tb.write_text(TB)
        exe = work / "sim"
        run(["iverilog", "-g2012", "-s", "tb", "-o", str(exe), str(SOURCE), str(tb)], work)
        actual = rows(run(["vvp", str(exe)], work))
        if actual != EXPECTED:
            raise RuntimeError(f"Icarus rows {actual} != {EXPECTED}")
        print("Icarus Verilog 13.0: five rows MATCH")
        if shutil.which("xrun"):
            actual = rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                               "-top", "tb", str(SOURCE), str(tb)], work))
            if actual != EXPECTED:
                raise RuntimeError(f"Xcelium rows {actual} != {EXPECTED}")
            print("Xcelium Verilog 24.03-s004: five rows MATCH")
        else:
            print("Xcelium Verilog 24.03-s004: no result, xrun unavailable")


if __name__ == "__main__":
    main()
