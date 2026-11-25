#!/usr/bin/env python3
"""Differential receipt for generated packed-element writes from an unpacked declaration."""
import os
from pathlib import Path
import os
import signal
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [["a=0", "y=0000"], ["a=1", "y=0101"],
            ["a=2", "y=1010"], ["a=3", "y=1111"],
            ["a=4", "y=xxxx"]]


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
module prefix_adder_unpacked_array_tb;
  logic [3:0] a; wire [3:0] y;
  prefix_adder_unpacked_array dut(.a(a), .y(y));
  initial begin
    a = 4'b0000; #1 $display("ROW a=0 y=%b", y);
    a = 4'b0101; #1 $display("ROW a=1 y=%b", y);
    a = 4'b1010; #1 $display("ROW a=2 y=%b", y);
    a = 4'b1111; #1 $display("ROW a=3 y=%b", y);
    a = 4'bxxxx; #1 $display("ROW a=4 y=%b", y);
    $finish;
  end
endmodule
'''


def main():
    generated = HERE / "prefix_adder_unpacked_array.sv.json"
    with tempfile.NamedTemporaryFile(suffix=".json") as temp:
        run(["python3", "extractors/sv/extract.py", "--top",
             "prefix_adder_unpacked_array", "-o", temp.name,
             str((HERE / "prefix_adder_unpacked_array.sv").relative_to(ROOT))])
        if Path(temp.name).read_bytes() != generated.read_bytes():
            raise RuntimeError("extractor envelope is not reproducible")
    print("extractor: generated-array envelope regenerates byte-identically")

    run(["lake", "build",
         "Examples.«system-verilog».sem2.prefix_adder_unpacked_array.agree"])
    actual = rows(run(["lake", "env", "lean", "--run", str(HERE / "oracle.lean")]))
    if actual != EXPECTED:
        raise RuntimeError(f"E: {actual!r} != {EXPECTED!r}")
    print("E: 5 generated-element rows MATCH")

    source = str(HERE / "prefix_adder_unpacked_array.sv")
    with tempfile.TemporaryDirectory(prefix="sv-prefix-array-") as work:
        work = Path(work)
        tb = work / "tb.sv"
        tb.write_text(testbench())
        exe = work / "sim"
        run(["iverilog", "-g2012", "-s", "prefix_adder_unpacked_array_tb",
             "-o", str(exe), source, str(tb)], work)
        actual = rows(run(["vvp", str(exe)], work))
    if actual != EXPECTED:
        raise RuntimeError(f"iverilog: {actual!r} != {EXPECTED!r}")
    print(run(["iverilog", "-V"]).splitlines()[0] + ": 5 source rows MATCH E")

    with tempfile.TemporaryDirectory(prefix="sv-prefix-array-xcelium-") as work:
        work = Path(work)
        tb = work / "tb.sv"
        tb.write_text(testbench())
        oracle_bin = os.environ.get("SV_ORACLE", "xrun")
        actual = rows(run([oracle_bin, "-sv", "-q",
                           "-timescale", "1ns/1ps", "-top",
                           "prefix_adder_unpacked_array_tb", source, str(tb)], work))
    if actual != EXPECTED:
        raise RuntimeError(f"xcelium: {actual!r} != {EXPECTED!r}")
    print("Xcelium reference simulator: 5 source rows MATCH E")


if __name__ == "__main__":
    main()
