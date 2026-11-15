#!/usr/bin/env python3
from pathlib import Path
import os, signal, subprocess, tempfile, shutil
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
def run(cmd, cwd=ROOT):
    p = subprocess.Popen(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, start_new_session=True)
    try: out, _ = p.communicate(timeout=120)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL); out, _ = p.communicate(); raise RuntimeError("timeout\n" + out)
    if p.returncode: raise RuntimeError(out)
    return out
def rows(text): return [line.split()[1:] for line in text.splitlines() if line.startswith("ROW ")]
def main():
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    expected = [["i=0", "y=1"], ["i=1", "y=1"], ["i=2", "y=1"], ["i=3", "y=1"], ["i=4", "y=z"], ["i=5", "y=1"], ["i=6", "y=0"], ["i=7", "y=1"]]
    print("E: 8 generated-child rows MATCH")
    src = str(HERE / "generate_unbound_parameter.sv")
    tb = str(HERE / "generate_unbound_parameter_canonical_e_tb.sv")
    with tempfile.TemporaryDirectory(prefix="sv-e-generate-unbound-") as w:
        exe = str(Path(w) / "sim")
        run(["iverilog", "-g2012", "-s", "generate_unbound_parameter_canonical_e_tb", "-o", exe, src, tb], w)
        actual = rows(run(["vvp", exe], w))
    if actual != expected: raise RuntimeError(f"Icarus Verilog 13.0: {actual} != {expected}")
    print("Icarus Verilog 13.0: 8 rows MATCH E")
    if shutil.which("xrun"):
        with tempfile.TemporaryDirectory(prefix="sv-e-generate-unbound-xcelium-") as w:
            actual = rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "generate_unbound_parameter_canonical_e_tb", src, tb], w))
        if actual != expected: raise RuntimeError(f"Xcelium: {actual} != {expected}")
        print("Xcelium 24.03-s004: 8 rows MATCH E")
if __name__ == "__main__": main()
