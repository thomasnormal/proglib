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

EXPECTED = {
    "iverilog": [
        "ROW R1 xclock a=x b=x",
        "ROW R2 xclock a=x b=x",
        "ROW R3 xclock a=x b=x",
        "ROW R4 xclock a=x b=x",
        "ROW R5 xclock a=x b=x",
        "ROW R6 xclock a=x b=x",
        "ROW R7 swap a=0 b=1",
        "ROW R8 swap a=1 b=0",
        "ROW R9 swap a=1 b=0",
        "ROW R10 swap a=1 b=0",
        "ROW R11 no-edge a=1 b=0",
        "ROW R12 race a=0",
        "ROW R13 race a=1",
        "ROW R14 caseeq a=x b=1",
        "ROW R15 wake g=1 count=3",
        "ROW R16 wake g=1 count=4",
        "ROW R17 unknown-index idx=x a=xxxx",
        "ROW R18 caseeq-index a=0010",
        "ROW R19 x-if a=x p=0 q=0",
        "ROW R20 x-if a=x p=0 q=0",
        "ROW R21 ternary a=x b=x",
        "ROW R22 xor a=x b=x",
        "ROW R23 nba-xclock g=x",
        "ROW R24 casez a=x b=1",
        "ROW R25 casex a=x b=1",
    ],
    "xrun": [
        "ROW R1 xclock a=x b=x",
        "ROW R2 xclock a=x b=x",
        "ROW R3 xclock a=x b=x",
        "ROW R4 xclock a=x b=x",
        "ROW R5 xclock a=x b=x",
        "ROW R6 xclock a=x b=x",
        "ROW R7 swap a=0 b=1",
        "ROW R8 swap a=1 b=0",
        "ROW R9 swap a=1 b=0",
        "ROW R10 swap a=1 b=0",
        "ROW R11 no-edge a=1 b=0",
        "ROW R12 race a=1",
        "ROW R13 race a=0",
        "ROW R14 caseeq a=x b=1",
        "ROW R15 wake g=1 count=3",
        "ROW R16 wake g=1 count=4",
        "ROW R17 unknown-index idx=x a=xxxx",
        "ROW R18 caseeq-index a=0010",
        "ROW R19 x-if a=x p=0 q=0",
        "ROW R20 x-if a=x p=0 q=0",
        "ROW R21 ternary a=x b=x",
        "ROW R22 xor a=x b=x",
        "ROW R23 nba-xclock g=x",
        "ROW R24 casez a=x b=1",
        "ROW R25 casex a=x b=1",
    ],
}

TB = r'''module nd_rows_tb;
  logic ca=0, cb=0, c=0, a_in=0, idx=0, seed=1; wire sa, sb;
  logic xca=1'bx, xcb=1'bx; wire xa, xb;
  logic case_a; wire case_b, casez_b, casex_b; wire [3:0] mem_a, case_idx_a; wire p,q; wire ternary_b,xor_b;
  logic wake_clk=0; wire wake_g; wire [31:0] wake_count;
  wire race01_a, race10_a, nba_xg;
  nd_rows_swap swap(.clk_a(ca),.clk_b(cb),.seed(seed),.a(sa),.b(sb));
  nd_rows_xclock xclock(.clk_a(xca),.clk_b(xcb),.a(xa),.b(xb));
  nd_rows_race01 race01(.clk(c),.a(race01_a));
  nd_rows_race10 race10(.clk(c),.a(race10_a));
  nd_rows_caseeq caseeq(.clk(c),.a(case_a),.b(case_b));
  nd_rows_casez casez_case(.clk(c),.a(case_a),.b(casez_b));
  nd_rows_casex casex_case(.clk(c),.a(case_a),.b(casex_b));
  nd_rows_caseeq_index caseeq_index(.clk(c),.a(case_idx_a));
  nd_rows_unknown_index unknown_index(.clk(c),.idx(idx),.a(mem_a));
  nd_rows_x_if x_if(.clk(c),.a(a_in),.p(p),.q(q));
  nd_rows_ternary ternary(.clk(c),.a(a_in),.b(ternary_b));
  nd_rows_xor xor_case(.clk(c),.a(a_in),.b(xor_b));
  nd_rows_nba_xclock nba_xclock(.clk(c),.g(nba_xg));
  nd_rows_wake wake(.clk(wake_clk),.g(wake_g),.count(wake_count));
  initial begin
    case_a=1'bx; a_in=1'bx; idx=1'bx;
    #1; $display("ROW R1 xclock a=%b b=%b",xa,xb);
    xca=1; xcb=1; #1;
    $display("ROW R2 xclock a=%b b=%b",xa,xb);
    xca=0; xcb=0; #1; xca=1; xcb=1; #1;
    $display("ROW R3 xclock a=%b b=%b",xa,xb);
    $display("ROW R4 xclock a=%b b=%b",xa,xb);
    xca=0; xcb=0; #1;
    $display("ROW R5 xclock a=%b b=%b",xa,xb);
    $display("ROW R6 xclock a=%b b=%b",xa,xb);
    ca=1; cb=1; #1; $display("ROW R7 swap a=%b b=%b",sa,sb); ca=0; cb=0;
    seed=0; #1; ca=1; cb=1; #1; $display("ROW R8 swap a=%b b=%b",sa,sb); ca=0; cb=0;
    seed=1; #1; ca=1; cb=1; #1; seed=0; ca=0; cb=0; #1; ca=1; cb=1; #1;
    $display("ROW R9 swap a=%b b=%b",sa,sb); $display("ROW R10 swap a=%b b=%b",sa,sb);
    ca=0; cb=0; #1; $display("ROW R11 no-edge a=%b b=%b",sa,sb);
    c=1; #1;
    $display("ROW R12 race a=%b",race01_a);
    $display("ROW R13 race a=%b",race10_a);
    $display("ROW R14 caseeq a=%b b=%b",case_a,case_b);
    c=0; #1;
    wake_clk=1; #1; $display("ROW R15 wake g=%b count=%0d",wake_g,wake_count);
    wake_clk=0; #1; wake_clk=1; #1; $display("ROW R16 wake g=%b count=%0d",wake_g,wake_count);
    c=1; #1;
    $display("ROW R17 unknown-index idx=%b a=%b",idx,mem_a);
    $display("ROW R18 caseeq-index a=%b",case_idx_a);
    $display("ROW R19 x-if a=%b p=%b q=%b",a_in,p,q);
    $display("ROW R20 x-if a=%b p=%b q=%b",a_in,p,q);
    $display("ROW R21 ternary a=%b b=%b",a_in,ternary_b);
    $display("ROW R22 xor a=%b b=%b",a_in,xor_b);
    $display("ROW R23 nba-xclock g=%b",nba_xg);
    $display("ROW R24 casez a=%b b=%b",case_a,casez_b);
    $display("ROW R25 casex a=%b b=%b",case_a,casex_b);
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
        expected = EXPECTED[simulator]
        if actual != expected:
            raise RuntimeError(f"{simulator}: expected {expected!r}, got {actual!r}")
        print(f"{simulator}: {len(actual)} rows MATCH")


if __name__ == "__main__":
    main()
