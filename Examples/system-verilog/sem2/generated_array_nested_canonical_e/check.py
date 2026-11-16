#!/usr/bin/env python3
"""Differential receipt for a nested generated-array packed select."""
from pathlib import Path
import os
import shutil
import signal
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [
    ["W=4", "i=0", "y=xxxxxxxx"],
    ["W=4", "i=1", "y=00000000"],
    ["W=4", "i=2", "y=00111101"],
    ["W=4", "i=3", "y=xxxxxxxx"],
    ["W=4", "i=4", "y=xxxxxx10"],
    ["W=4", "i=5", "y=xxxxxxxz"],
    ["W=4", "i=6", "y=xxxxxxx1"],
    ["W=4", "i=7", "y=00000101"],
    ["W=8", "i=0", "y=xxxxxxxx"],
    ["W=8", "i=1", "y=00000000"],
    ["W=8", "i=2", "y=01111101"],
    ["W=8", "i=3", "y=xxxxxxxx"],
    ["W=8", "i=4", "y=xxxxxx10"],
    ["W=8", "i=5", "y=xxxxxxxz"],
    ["W=8", "i=6", "y=xxxxxxx1"],
    ["W=8", "i=7", "y=01010101"],
]


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


def testbench(width):
    return f'''`timescale 1ns/1ps
module generated_array_nested_canonical_e_tb;
  parameter integer P = {width};
  logic [P-1:0] x, taps; wire [7:0] y;
  generated_array_nested_canonical_e #(.W(P)) dut(.x(x), .taps(taps), .y(y));
  initial begin
    #1 $display("ROW W=%0d i=0 y=%b", P, y);
    x='0; taps='0; #1 $display("ROW W=%0d i=1 y=%b", P, y);
    if (P == 4) begin x=4'h5; taps=4'hc; end else begin x=8'ha5; taps=8'h3c; end
    #1 $display("ROW W=%0d i=2 y=%b", P, y);
    x='x; taps='h1; #1 $display("ROW W=%0d i=3 y=%b", P, y);
    if (P == 4) x=4'h6; else x=8'h12;
    taps='x; #1 $display("ROW W=%0d i=4 y=%b", P, y);
    x='z; if (P == 4) taps=4'h3; else taps=8'h3;
    #1 $display("ROW W=%0d i=5 y=%b", P, y);
    if (P == 4) x=4'h9; else x=8'h81;
    taps='z; #1 $display("ROW W=%0d i=6 y=%b", P, y);
    x='1; taps='h1; #1 $display("ROW W=%0d i=7 y=%b", P, y);
    $finish;
  end
endmodule
'''


def main():
    generated = HERE / "generated_array_nested_canonical_e.sv.json"
    with tempfile.NamedTemporaryFile(suffix=".json") as temp:
        run(["python3", "extractors/sv/extract.py", "--top",
             "generated_array_nested_canonical_e", "--retain-proc-rewrites",
             "-o", temp.name,
             str((HERE / "generated_array_nested_canonical_e.sv").relative_to(ROOT))])
        if Path(temp.name).read_bytes() != generated.read_bytes():
            raise RuntimeError("extractor envelope is not reproducible")
    print("extractor: retained nested-select envelope regenerates byte-identically")

    run(["lake", "build",
         "Examples.«system-verilog».sem2.generated_array_nested_canonical_e.agree"])
    refusal = run(["lake", "env", "lean", "--run", str(HERE / "oracle.lean")])
    topology = ("10.3: continuous assignment target is read from itself or a later "
                "assignment; canonical E requires topological source order")
    expected_refusals = [
        f"E REFUSAL W=4: {topology}",
        f"E REFUSAL W=8: {topology}",
    ]
    actual_refusals = [line for line in refusal.splitlines()
                       if line.startswith("E REFUSAL ")]
    if actual_refusals != expected_refusals:
        raise RuntimeError(f"unexpected E refusals: {actual_refusals}")
    print("E: exact §10.3 topology refusal at W=4 and W=8")

    simulators = ["iverilog"]
    if shutil.which("xrun"):
        simulators.append("xrun")
    source = str(HERE / "generated_array_nested_canonical_e.sv")
    for simulator in simulators:
        actual = []
        for width in (4, 8):
            with tempfile.TemporaryDirectory(prefix="sv-nested-array-") as work:
                tb = Path(work) / "tb.sv"
                tb.write_text(testbench(width))
                if simulator == "iverilog":
                    exe = str(Path(work) / "sim")
                    run(["iverilog", "-g2012", "-s",
                         "generated_array_nested_canonical_e_tb", "-o", exe,
                         source, str(tb)], work)
                    actual.extend(rows(run(["vvp", exe], work)))
                else:
                    actual.extend(rows(run(["xrun", "-sv", "-q", "-timescale",
                                            "1ns/1ps", "-top",
                                            "generated_array_nested_canonical_e_tb",
                                            source, str(tb)], work)))
        if actual != EXPECTED:
            raise RuntimeError(f"{simulator}: {actual} != {EXPECTED}")
        version = run(["iverilog", "-V"] if simulator == "iverilog"
                      else ["xrun", "-version"]).splitlines()[0]
        print(f"{version}: {len(actual)} source rows MATCH the refusal receipt")


if __name__ == "__main__":
    main()
