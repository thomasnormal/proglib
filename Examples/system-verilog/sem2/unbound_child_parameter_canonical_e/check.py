#!/usr/bin/env python3
"""Differential receipt for a default-width child parameter."""
from pathlib import Path
import shutil
import subprocess
import tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]

def run(cmd, cwd=ROOT):
    return subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, check=True, timeout=180).stdout

def rows(text):
    return [line.split()[1:] for line in text.splitlines() if line.startswith("ROW ")]

def main():
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    expected = [["i=0", "y=00000000"], ["i=1", "y=00000001"],
                ["i=2", "y=00101010"], ["i=3", "y=11111111"],
                ["i=4", "y=xxxxxxxx"], ["i=5", "y=zzzzzzzz"],
                ["i=6", "y=01111111"], ["i=7", "y=10000000"]]
    source = HERE / "unbound_child_parameter.sv"
    tb = HERE / "unbound_child_parameter_canonical_e_tb.sv"
    with tempfile.TemporaryDirectory(prefix="sv-e-unbound-child-") as work:
        work = Path(work)
        exe = str(work / "sim")
        run(["iverilog", "-g2012", "-s", "unbound_child_parameter_canonical_e_tb",
             "-o", exe, str(source), str(tb)], work)
        actual = rows(run(["vvp", exe], work))
    if actual != expected:
        raise RuntimeError(f"Icarus Verilog 13.0: {actual} != {expected}")
    print("E: 8 rows MATCH")
    print("Icarus Verilog 13.0: 8 rows MATCH E")
    if shutil.which("xrun"):
        with tempfile.TemporaryDirectory(prefix="sv-e-unbound-child-xcelium-") as work:
            actual = rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                               "-top", "unbound_child_parameter_canonical_e_tb",
                               str(source), str(tb)], Path(work)))
        if actual != expected:
            raise RuntimeError(f"Xcelium 24.03-s004: {actual} != {expected}")
        print("Xcelium 24.03-s004: 8 rows MATCH E")

if __name__ == "__main__":
    main()
