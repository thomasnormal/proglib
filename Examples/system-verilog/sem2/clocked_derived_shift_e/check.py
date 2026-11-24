#!/usr/bin/env python3
"""Differential receipt for the derived continuous-assignment clocked route."""
from pathlib import Path
import os
import shutil
import signal
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [
    ["i=0", "q=0000"], ["i=1", "q=0000"], ["i=2", "q=0010"],
    ["i=3", "q=0010"], ["i=4", "q=0100"], ["i=5", "q=0100"],
    ["i=6", "q=0101"], ["i=7", "q=0101"], ["i=8", "q=1010"],
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

def tb():
    return '''module clocked_derived_shift_e_tb;
  logic clk, rst_n, load;
  logic [3:0] d, mask;
  wire [3:0] q, observed;
  clocked_derived_shift_e #(.N(4)) dut(.*);
  initial begin
    clk=0; rst_n=0; load=0; d=0; mask=0; #1 $display("ROW i=0 q=%b", q);
    rst_n=1; load=1; d=4'd3; mask=4'd1; #1 $display("ROW i=1 q=%b", q);
    clk=1; #1 $display("ROW i=2 q=%b", q);
    clk=0; load=0; mask=4'd2; #1 $display("ROW i=3 q=%b", q);
    clk=1; #1 $display("ROW i=4 q=%b", q);
    clk=0; load=1; d=4'd9; mask=4'd4; #1 $display("ROW i=5 q=%b", q);
    clk=1; #1 $display("ROW i=6 q=%b", q);
    clk=0; load=0; d=4'bxxxx; mask=4'bxxxx; #1 $display("ROW i=7 q=%b", q);
    clk=1; #1 $display("ROW i=8 q=%b", q);
    $finish;
  end
endmodule
'''

def main():
    generated = HERE / "clocked_derived_shift_e.sv.json"
    with tempfile.NamedTemporaryFile(suffix=".json") as temp:
        run(["python3", "extractors/sv/extract.py", "--top",
             "clocked_derived_shift_e", "-o", temp.name,
             str((HERE / "clocked_derived_shift_e.sv").relative_to(ROOT))])
        if Path(temp.name).read_bytes() != generated.read_bytes():
            raise RuntimeError("extractor envelope is stale")
    run(["lake", "build",
         "Examples.«system-verilog».sem2.clocked_derived_shift_e.agree"])
    actual_e = rows(run(["lake", "env", "lean", "--run", str(HERE / "oracle.lean")]))
    if actual_e != EXPECTED:
        raise RuntimeError(f"E: {actual_e} != {EXPECTED}")
    print("extractor: envelope regenerates byte-identically")
    print("E: 9 derived-clocked rows MATCH")
    for simulator in ["iverilog"] + (["xrun"] if shutil.which("xrun") else []):
        with tempfile.TemporaryDirectory(prefix="sv-derived-shift-") as work:
            tb_path = Path(work) / "tb.sv"
            tb_path.write_text(tb())
            source = str(HERE / "clocked_derived_shift_e.sv")
            if simulator == "iverilog":
                exe = str(Path(work) / "sim")
                run(["iverilog", "-g2012", "-s", "clocked_derived_shift_e_tb",
                     "-o", exe, source, str(tb_path)], work)
                actual = rows(run(["vvp", exe], work))
                version = run(["iverilog", "-V"]).splitlines()[0]
            else:
                actual = rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                                   "-top", "clocked_derived_shift_e_tb", source,
                                   str(tb_path)], work))
                version = run(["xrun", "-version"]).splitlines()[0]
            if actual != EXPECTED:
                raise RuntimeError(f"{simulator}: {actual} != {EXPECTED}")
            print(f"{version}: {len(actual)} rows MATCH E")

if __name__ == "__main__":
    main()
