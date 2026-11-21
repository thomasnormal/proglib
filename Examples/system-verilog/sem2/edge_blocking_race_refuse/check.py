#!/usr/bin/env python3
"""Differential receipt for the refused same-edge blocking race."""
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
ROWS = [("0", "0"), ("1", "1"), ("0", "0"), ("1", "0"), ("0", "1"), ("1", "x")]
SOURCES = {
    "edge_blocking_race_refuse": {"expected_iverilog": ["xx", "1x", "1x", "00", "00", "x0"], "expected_xrun": ["xx", "1x", "1x", "01", "01", "x0"]},
    "edge_blocking_race_refuse2": {"expected_iverilog": ["xx", "11", "11", "01", "01", "xx"], "expected_xrun": ["xx", "11", "11", "00", "00", "xx"]},
}

def run(command, cwd=ROOT):
    process = subprocess.run(command, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180, check=False)
    if process.returncode:
        raise RuntimeError(f"{command[0]} exited {process.returncode}:\n{process.stdout}")
    return process.stdout

def tb(top):
    lines = ["module tb; logic clk = 1'b0, d = 1'b0; wire a, b;", f"  {top} dut(.clk(clk), .d(d), .a(a), .b(b));", "  initial begin #1 $display(\"ROW %b%b\", a, b);"]
    for clk, data in ROWS[1:]:
        lines.append(f"    clk = 1'b{clk}; d = 1'b{data}; #1 $display(\"ROW %b%b\", a, b);")
    lines += ["    $finish;", "  end", "endmodule", ""]
    return "\n".join(lines)

def source_rows(top, simulator):
    with tempfile.TemporaryDirectory(prefix="sv-edge-race-") as work:
        work = Path(work)
        tb_path = work / "tb.sv"; tb_path.write_text(tb(top))
        source = HERE / f"{top}.sv"
        if simulator == "iverilog":
            exe = work / "sim"; run(["iverilog", "-g2012", "-s", "tb", "-o", str(exe), str(source), str(tb_path)], work)
            output = run(["vvp", str(exe)], work)
        else:
            output = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "tb", str(source), str(tb_path)], work)
    return [line.split()[1] for line in output.splitlines() if line.startswith("ROW ")]

def main():
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    print("canonical E: both same-edge blocking races refuse")
    if not shutil.which("iverilog") or not shutil.which("vvp"):
        raise RuntimeError("Icarus is required")
    simulators = ["iverilog"]
    if shutil.which("xrun"): simulators.append("xrun")
    for simulator in simulators:
        key = "expected_xrun" if simulator == "xrun" else "expected_iverilog"
        for top, expected in SOURCES.items():
            actual = source_rows(top, simulator)
            if actual != expected[key]: raise RuntimeError(f"{top}/{simulator}: {actual} != {expected[key]}")
            print(f"{top}/{simulator}: {len(actual)} rows show schedule-dependent traces")

if __name__ == "__main__": main()
