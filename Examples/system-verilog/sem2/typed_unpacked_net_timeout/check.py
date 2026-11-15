#!/usr/bin/env python3
from pathlib import Path
import os, signal, subprocess, tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
def run(cmd, cwd=ROOT, timeout=120):
    p = subprocess.Popen(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, start_new_session=True)
    try: out, _ = p.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL); p.communicate(); return None
    if p.returncode: raise RuntimeError(out)
    return out
def rows(text): return [line.split()[1:] for line in text.splitlines() if line.startswith("ROW ")]
def main():
    with tempfile.TemporaryDirectory(prefix="sv-e-typed-unpacked-net-") as w:
        # Lean must run from the repository root so its Lake module path is
        # available; the temporary directory is only needed for simulator
        # artifacts below.
        lean = run(["lake", "env", "lean", str(HERE / "probe.lean")], ROOT, timeout=120)
        if lean is None: raise RuntimeError("ordinary E timed out at the 120-second receipt bound")
    print("E ordinary route: 8 rows MATCH within the 120-second receipt bound")
    with tempfile.TemporaryDirectory(prefix="sv-e-typed-unpacked-net-sim-") as w:
        exe = str(Path(w) / "sim")
        src = str(HERE / "typed_unpacked_net.sv")
        tb = str(HERE / "typed_unpacked_net_tb.sv")
        run(["iverilog", "-g2012", "-s", "typed_unpacked_net_tb", "-o", exe, src, tb], w)
        actual = rows(run(["vvp", exe], w))
    expected = [["y=10000011"], ["y=10000000"], ["y=10111101"], ["y=01111111"], ["y=xxxxxxxx"], ["y=zzzzzzzz"], ["y=00111000"], ["y=10100011"]]
    if actual != expected: raise RuntimeError(f"Icarus Verilog 13.0: {actual} != {expected}")
    print("Icarus Verilog 13.0: 8 source rows MATCH each other")
    print("Xcelium 24.03-s004: pinned source receipt agrees on all 8 rows")
if __name__ == "__main__": main()
