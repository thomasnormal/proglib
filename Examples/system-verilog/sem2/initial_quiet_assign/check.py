#!/usr/bin/env python3
"""Differential receipt for the quiet-start theorem counterexample."""
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCE = HERE / "initial_quiet_assign.sv"
ENV = HERE / "initial_quiet_assign.sv.json"
EXPECTED = ["1"]
TB = """module tb; wire y;
initial_quiet_assign dut(.y(y));
initial begin #1 $display("ROW y=%b", y); $finish; end
endmodule
"""


def run(args, cwd=ROOT):
    return subprocess.run(args, cwd=cwd, check=True, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT).stdout


def rows(output):
    return [line.split()[1].split("=", 1)[1] for line in output.splitlines()
            if line.startswith("ROW ")]


def main():
    with tempfile.NamedTemporaryFile(suffix=".json") as out:
        run(["python3", "extractors/sv/extract.py", "--top", "initial_quiet_assign",
             "--retain-proc-rewrites", "-o", out.name, str(SOURCE.relative_to(ROOT))])
        if Path(out.name).read_bytes() != ENV.read_bytes():
            raise RuntimeError("extractor envelope is not reproducible")
    run(["lake", "build",
         "Examples.«system-verilog».sem2.initial_quiet_assign.probe"])
    simulators = ["iverilog"]
    if shutil.which("xrun"):
        simulators.append("xrun")
    for simulator in simulators:
        with tempfile.TemporaryDirectory(prefix="sv-initial-quiet-") as work:
            tb = Path(work) / "tb.sv"
            tb.write_text(TB)
            if simulator == "iverilog":
                exe = Path(work) / "sim"
                run(["iverilog", "-g2012", "-s", "tb", "-o", str(exe),
                     str(SOURCE), str(tb)], Path(work))
                actual = rows(run(["vvp", str(exe)], Path(work)))
            else:
                actual = rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                                   "-top", "tb", str(SOURCE), str(tb)], Path(work)))
        if actual != EXPECTED:
            raise RuntimeError(f"{simulator}: {actual} != {EXPECTED}")
        print(f"{simulator}: 1 row MATCH y=1")
    print("E: initialState differs from declaration-initialized state after settle")


if __name__ == "__main__":
    main()
