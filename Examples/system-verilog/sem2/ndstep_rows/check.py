#!/usr/bin/env python3
"""Differential rows for every current choice-explicit step arm."""
from pathlib import Path
import os
import shutil
import signal
import subprocess
import tempfile
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
sys.path.insert(0, str(ROOT / "harness/sv"))
from xcelium_probe import probe_xcelium  # noqa: E402

EXPECTED = [
    "ROW swap-seed a=0 b=1",
    "ROW swap-after a=1 b=0",
    "ROW caseeq a=x b=1",
    "ROW unknown-index idx=x a=xxxx",
    "ROW x-if a=x p=0 q=0",
    "ROW ternary a=x b=x",
    "ROW xor a=x b=x",
    "ROW wake g=1 count=3",
]

TB = r'''module nd_rows_tb;
  logic ca=0, cb=0, c=0, a_in=0, idx=0, seed=1; wire sa, sb;
  logic case_a; wire case_b; wire [3:0] mem_a; wire p,q; wire ternary_b,xor_b;
  logic wake_clk=0; wire wake_g; wire [31:0] wake_count;
  nd_rows_swap swap(.clk_a(ca),.clk_b(cb),.seed(seed),.a(sa),.b(sb));
  nd_rows_caseeq caseeq(.clk(c),.a(case_a),.b(case_b));
  nd_rows_unknown_index unknown_index(.clk(c),.idx(idx),.a(mem_a));
  nd_rows_x_if x_if(.clk(c),.a(a_in),.p(p),.q(q));
  nd_rows_ternary ternary(.clk(c),.a(a_in),.b(ternary_b));
  nd_rows_xor xor_case(.clk(c),.a(a_in),.b(xor_b));
  nd_rows_wake wake(.clk(wake_clk),.g(wake_g),.count(wake_count));
  initial begin
    case_a=1'bx; a_in=1'bx; idx=1'bx;
    ca=1; cb=1; #1; $display("ROW swap-seed a=%b b=%b",sa,sb); ca=0; cb=0;
    seed=0; #1; ca=1; cb=1; #1; $display("ROW swap-after a=%b b=%b",sa,sb); ca=0; cb=0;
    c=1; #1;
    $display("ROW caseeq a=%b b=%b",case_a,case_b);
    $display("ROW unknown-index idx=%b a=%b",idx,mem_a);
    $display("ROW x-if a=%b p=%b q=%b",a_in,p,q);
    $display("ROW ternary a=%b b=%b",a_in,ternary_b);
    $display("ROW xor a=%b b=%b",a_in,xor_b);
    c=0; #1;
    wake_clk=1; #1; $display("ROW wake g=%b count=%0d",wake_g,wake_count);
    $finish;
  end
endmodule
'''


def run(args, cwd=ROOT):
    proc = subprocess.Popen(args, cwd=cwd, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                            start_new_session=True)
    try:
        out, err = proc.communicate(timeout=180)
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        out, err = proc.communicate()
        raise RuntimeError(f"{args[0]} timed out:\n{out}{err}")
    if proc.returncode:
        raise RuntimeError(f"{args[0]} exited {proc.returncode}:\n{out}{err}")
    return out


def rows(output):
    return [line for line in output.splitlines() if line.startswith("ROW ")]


def main():
    run(["lake", "env", "lean", str(HERE / "rows.lean")])
    print("E relation rows: 23 probes, rows file builds")
    if not shutil.which("iverilog") or not shutil.which("vvp"):
        raise RuntimeError("Icarus is required for this differential check")
    print(run(["iverilog", "-V"]).splitlines()[0])
    simulators = ["iverilog"]
    if shutil.which("xrun"):
        status, details = probe_xcelium()
        print(details)
        if status == 0:
            simulators.append("xrun")
        elif status == 77:
            print("no Xcelium result: explicit license refusal")
        else:
            raise RuntimeError("Xcelium readiness probe failed")
    else:
        print("no Xcelium result: xrun unavailable")
    source = str(HERE / "rows.sv")
    for simulator in simulators:
        with tempfile.TemporaryDirectory(prefix="sv-ndstep-rows-") as work:
            tb = Path(work) / "tb.sv"
            tb.write_text(TB)
            if simulator == "iverilog":
                exe = str(Path(work) / "sim")
                run(["iverilog", "-g2012", "-s", "nd_rows_tb", "-o", exe,
                     source, str(tb)], work)
                output = run(["vvp", exe], work)
            else:
                output = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                              "-top", "nd_rows_tb", source, str(tb)], work)
        actual = rows(output)
        if actual != EXPECTED:
            raise RuntimeError(f"{simulator}: expected {EXPECTED!r}, got {actual!r}")
        print(f"{simulator}: {len(actual)} rows MATCH")


if __name__ == "__main__":
    main()
