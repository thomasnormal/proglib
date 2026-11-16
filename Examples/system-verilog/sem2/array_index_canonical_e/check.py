#!/usr/bin/env python3
"""Differential receipt for a fixed unpacked-array element index."""
from pathlib import Path
import os
import shutil
import signal
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [["i=0", "y=xxxxxxxx"], ["i=1", "y=xxxxxxxx"],
            ["i=2", "y=xxxxxxxx"], ["i=3", "y=xxxxxxxx"],
            ["i=4", "y=xxxxxxxx"], ["i=5", "y=xxxxxxxx"],
            ["i=6", "y=xxxxxxxx"], ["i=7", "y=xxxxxxxx"]]


def run(args, cwd=ROOT, timeout=240):
    proc = subprocess.Popen(args, cwd=cwd, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, start_new_session=True)
    try:
        out, err = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        out, err = proc.communicate()
        raise RuntimeError(f"{args[0]} timed out:\n{out}{err}")
    if proc.returncode:
        raise RuntimeError(f"{args[0]} exited {proc.returncode}:\n{out}{err}")
    return out


def rows(output):
    return [line.split()[1:] for line in output.splitlines()
            if line.startswith("ROW ")]


def testbench():
    return '''`timescale 1ns/1ps
module array_index_canonical_e_tb;
  logic [1:0] i; wire [7:0] y;
  array_index_canonical_e dut(.i(i), .y(y));
  initial begin
    i = 2'b00; #1 $display("ROW i=0 y=%b", y);
    i = 2'b01; #1 $display("ROW i=1 y=%b", y);
    i = 2'b10; #1 $display("ROW i=2 y=%b", y);
    i = 2'b11; #1 $display("ROW i=3 y=%b", y);
    i = 2'bxx; #1 $display("ROW i=4 y=%b", y);
    i = 2'bzz; #1 $display("ROW i=5 y=%b", y);
    i = 2'b00; #1 $display("ROW i=6 y=%b", y);
    i = 2'b00; #1 $display("ROW i=7 y=%b", y);
    $finish;
  end
endmodule
'''


def main():
    generated = HERE / "array_index_canonical_e.sv.json"
    with tempfile.NamedTemporaryFile(suffix=".json") as temp:
        run(["python3", "extractors/sv/extract.py", "--top",
             "array_index_canonical_e", "-o", temp.name,
             str((HERE / "array_index_canonical_e.sv").relative_to(ROOT))])
        if Path(temp.name).read_bytes() != generated.read_bytes():
            raise RuntimeError("extractor envelope is not reproducible")
    print("extractor: fixed-array index envelope regenerates byte-identically")

    run(["lake", "build",
         "Examples.«system-verilog».sem2.array_index_canonical_e.agree"])
    actual = rows(run(["lake", "env", "lean", "--run", str(HERE / "oracle.lean")]))
    if actual != EXPECTED:
        raise RuntimeError(f"E: {actual!r} != {EXPECTED!r}")
    print("E: 8 fixed-array index rows (known, x, z)")

    source = str(HERE / "array_index_canonical_e.sv")
    simulators = ["iverilog"] + (["xrun"] if shutil.which("xrun") else [])
    for simulator in simulators:
        with tempfile.TemporaryDirectory(prefix="sv-array-index-") as work:
            work = Path(work)
            tb = work / "tb.sv"
            tb.write_text(testbench())
            if simulator == "iverilog":
                exe = work / "sim"
                run(["iverilog", "-g2012", "-s", "array_index_canonical_e_tb",
                     "-o", str(exe), source, str(tb)], work)
                actual = rows(run(["vvp", str(exe)], work))
            else:
                actual = rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                                   "-top", "array_index_canonical_e_tb", source,
                                   str(tb)], work))
        if actual != EXPECTED:
            raise RuntimeError(f"{simulator}: {actual!r} != {EXPECTED!r}")
        version = run(["iverilog", "-V"] if simulator == "iverilog"
                      else ["xrun", "-version"]).splitlines()[0]
        print(f"{version}: 8 source rows MATCH E")


if __name__ == "__main__":
    main()
