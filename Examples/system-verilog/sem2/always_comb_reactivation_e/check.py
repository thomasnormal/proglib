#!/usr/bin/env python3
"""Differential receipt for §9.2.2.2.1 always_comb self-write sensitivity."""
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]

CASES = {
    "rbw_comb": {
        "source": ROOT / "Examples/system-verilog/sem2/rbw_comb/rbw_comb.sv",
        "decl": "logic [1:0] a = 2'b00;",
        "ports": "wire [1:0] y;",
        "instance": "rbw_comb dut(.a(a), .y(y));",
        "rows": [("a", "00"), ("a", "01"), ("a", "01"), ("a", "10"), ("a", "1x"), ("a", "00")],
        "expected": ["xx", "00", "00", "01", "10", "1x"],
    },
    "rbw_held": {
        "source": ROOT / "Examples/system-verilog/sem2/rbw_held/rbw_held.sv",
        "decl": "logic c = 1'b0; logic [1:0] a = 2'b00, b = 2'b00;",
        "ports": "wire [1:0] y;",
        "instance": "rbw_held dut(.c(c), .a(a), .b(b), .y(y));",
        "rows": [
            ("c", "0", "a", "00", "b", "00"),
            ("c", "1", "a", "01", "b", "00"),
            ("c", "0", "a", "01", "b", "01"),
            ("c", "1", "a", "00", "b", "01"),
            ("c", "x", "a", "01", "b", "00"),
            ("c", "1", "a", "01", "b", "00"),
            ("c", "0", "a", "00", "b", "01"),
            ("c", "z", "a", "01", "b", "01"),
        ],
        "expected": ["xx", "01", "00", "00", "01", "01", "00", "01"],
    },
    "rbw_selfinc": {
        "source": ROOT / "Examples/system-verilog/sem2/rbw_selfinc/rbw_selfinc.sv",
        "decl": "logic a = 1'b1;",
        "ports": "wire [1:0] y;",
        "instance": "rbw_selfinc dut(.a(a), .y(y));",
        "rows": [("a", "1"), ("a", "0"), ("a", "1"), ("a", "1"), ("a", "x"), ("a", "0"), ("a", "1")],
        "expected": ["x1", "10", "01", "01", "1x", "x0", "01"],
    },
}


def run(command, cwd=ROOT):
    process = subprocess.run(command, cwd=cwd, text=True, stdout=subprocess.PIPE,
                             stderr=subprocess.STDOUT, timeout=180, check=False)
    if process.returncode:
        raise RuntimeError(f"{command[0]} exited {process.returncode}:\n{process.stdout}")
    return process.stdout


def tb(case):
    first = case["rows"][0]
    init = " ".join(f"{first[i]} = {len(first[i + 1])}'b{first[i + 1]};"
                    for i in range(0, len(first), 2))
    lines = ["module tb;", f"  {case['decl']}", f"  {case['ports']}",
             f"  {case['instance']}", "  initial begin", "    #1 $display(\"ROW %b\", y);"]
    for row in case["rows"][1:]:
        update = " ".join(f"{row[i]} = {len(row[i + 1])}'b{row[i + 1]};"
                           for i in range(0, len(row), 2))
        lines.append(f"    {update} #1 $display(\"ROW %b\", y);")
    lines += ["    $finish;", "  end", "endmodule", ""]
    return "\n".join(lines)


def source_rows(case, simulator):
    with tempfile.TemporaryDirectory(prefix=".sv-comb-reactivation-", dir=ROOT) as work:
        work = Path(work)
        tb_path = work / "tb.sv"
        tb_path.write_text(tb(case))
        if simulator == "iverilog":
            exe = work / "sim"
            run(["iverilog", "-g2012", "-s", "tb", "-o", str(exe),
                 str(case["source"]), str(tb_path)], work)
            output = run(["vvp", str(exe)], work)
        else:
            output = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                          "-top", "tb", str(case["source"]), str(tb_path)], work)
    return [line.split()[1] for line in output.splitlines() if line.startswith("ROW ")]


def main():
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    print("canonical E: AlwaysComb:self-read refusal")
    if not shutil.which("iverilog") or not shutil.which("vvp"):
        raise RuntimeError("Icarus is required")
    simulators = ["iverilog"]
    if shutil.which("xrun"):
        simulators.append("xrun")
    for simulator in simulators:
        for name, case in CASES.items():
            actual = source_rows(case, simulator)
            if actual != case["expected"]:
                raise RuntimeError(f"{name}/{simulator}: {actual} != {case['expected']}")
            print(f"{name}/{simulator}: {len(actual)} rows MATCH pinned simulator expectations")


if __name__ == "__main__":
    main()
