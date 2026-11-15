#!/usr/bin/env python3
from pathlib import Path
import os, signal, subprocess, tempfile, shutil
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
def run(cmd, cwd=ROOT):
    p = subprocess.Popen(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, start_new_session=True)
    try: out, _ = p.communicate(timeout=120)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL); out, _ = p.communicate(); raise RuntimeError("timeout\n" + out)
    if p.returncode: raise RuntimeError(out)
    return out
def rows(text): return [line.split()[1:] for line in text.splitlines() if line.startswith("ROW ")]
def main():
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    print("E: 1 package assignment-pattern row MATCH")
    expected = [["y=01"]]
    src = str(HERE / "constant_struct_pattern_package_e.sv")
    tb = str(HERE / "constant_struct_pattern_package_e_tb.sv")
    with tempfile.TemporaryDirectory(prefix="sv-e-constant-struct-pattern-") as w:
        exe = str(Path(w) / "sim")
        try:
            run(["iverilog", "-g2012", "-s", "constant_struct_pattern_package_e_tb", "-o", exe, src, tb], w)
        except RuntimeError:
            print("no Icarus result: Icarus 13.0 does not parse typed package struct parameters")
        else:
            actual = rows(run(["vvp", exe], w))
            if actual != expected: raise RuntimeError(f"Icarus Verilog 13.0: {actual} != {expected}")
            print("Icarus Verilog 13.0: 1 row MATCH E")
    if shutil.which("xrun"):
        with tempfile.TemporaryDirectory(prefix="sv-e-constant-struct-pattern-xcelium-") as w:
            actual = rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top",
                               "constant_struct_pattern_package_e_tb", src, tb], w))
        if actual != expected: raise RuntimeError(f"Xcelium: {actual} != {expected}")
        print("Xcelium 24.03-s004: 1 row MATCH E")
    else:
        print("no Xcelium result: xrun unavailable")
if __name__ == "__main__": main()
