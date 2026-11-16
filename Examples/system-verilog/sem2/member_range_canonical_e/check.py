#!/usr/bin/env python3
"""Differential receipt for a generated packed-member range select."""
from pathlib import Path
import os
import shutil
import signal
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [["i=0", "result=xx"], ["i=1", "result=00"],
            ["i=2", "result=11"], ["i=3", "result=00"],
            ["i=4", "result=xx"], ["i=5", "result=zz"],
            ["i=6", "result=11"]]


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
module member_range_canonical_e_tb;
  logic [7:0] bits; wire [1:0] result;
  member_range_canonical_e dut(.bits(bits), .result(result));
  initial begin
    bits = 8'bxxxxxxxx; #1 $display("ROW i=0 result=%b", result);
    bits = 8'b00000000; #1 $display("ROW i=1 result=%b", result);
    bits = 8'b00000011; #1 $display("ROW i=2 result=%b", result);
    bits = 8'b11111100; #1 $display("ROW i=3 result=%b", result);
    bits = 8'bxxxxxxxx; #1 $display("ROW i=4 result=%b", result);
    bits = 8'bzzzzzzzz; #1 $display("ROW i=5 result=%b", result);
    bits = 8'b11111111; #1 $display("ROW i=6 result=%b", result);
    $finish;
  end
endmodule
'''


def main():
    generated = HERE / "member_range_canonical_e.sv.json"
    with tempfile.NamedTemporaryFile(suffix=".json") as temp:
        run(["python3", "extractors/sv/extract.py", "--top",
             "member_range_canonical_e", "--retain-proc-rewrites",
             "-o", temp.name,
             str((HERE / "member_range_canonical_e.sv").relative_to(ROOT))])
        if Path(temp.name).read_bytes() != generated.read_bytes():
            raise RuntimeError("extractor envelope is not reproducible")
    print("extractor: generated-member range envelope regenerates byte-identically")

    run(["lake", "build",
         "Examples.«system-verilog».sem2.member_range_canonical_e.agree"])
    actual = rows(run(["lake", "env", "lean", "--run", str(HERE / "oracle.lean")]))
    if actual != EXPECTED:
        raise RuntimeError(f"E: {actual!r} != {EXPECTED!r}")
    print("E: 7 generated-member range rows (known, x, z)")

    source = str(HERE / "member_range_canonical_e.sv")
    simulators = ["iverilog"] + (["xrun"] if shutil.which("xrun") else [])
    for simulator in simulators:
        with tempfile.TemporaryDirectory(prefix="sv-member-range-") as work:
            work = Path(work)
            tb = work / "tb.sv"
            tb.write_text(testbench())
            if simulator == "iverilog":
                exe = work / "sim"
                run(["iverilog", "-g2012", "-s", "member_range_canonical_e_tb",
                     "-o", str(exe), source, str(tb)], work)
                actual = rows(run(["vvp", str(exe)], work))
            else:
                actual = rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                                   "-top", "member_range_canonical_e_tb", source,
                                   str(tb)], work))
        if actual != EXPECTED:
            raise RuntimeError(f"{simulator}: {actual!r} != {EXPECTED!r}")
        version = run(["iverilog", "-V"] if simulator == "iverilog"
                      else ["xrun", "-version"]).splitlines()[0]
        print(f"{version}: 7 source rows MATCH E")


if __name__ == "__main__":
    main()
