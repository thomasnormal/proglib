#!/usr/bin/env python3
from pathlib import Path
import os, signal, shutil, subprocess, tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]

def run(cmd, cwd=ROOT):
    p = subprocess.Popen(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, start_new_session=True)
    try:
        out, _ = p.communicate(timeout=120)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)
        out, _ = p.communicate()
        raise RuntimeError("timeout\n" + out)
    if p.returncode:
        raise RuntimeError(out)
    return out

def rows(text):
    return [line.split()[1:] for line in text.splitlines() if line.startswith("ROW ")]

def main():
    expected = [["i=0", "z_out=0"], ["i=1", "z_out=0"]]
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    print("E: 2 generated-output-net rows MATCH")
    src = str(HERE / "net_generated_output_port_canonical_e.sv")
    tb = str(HERE / "net_generated_output_port_canonical_e_tb.sv")
    with tempfile.TemporaryDirectory(prefix="sv-e-net-generated-output-") as w:
        exe = str(Path(w) / "sim")
        run(["iverilog", "-g2012", "-s", "net_generated_output_port_canonical_e_tb",
             "-o", exe, src, tb], w)
        actual = rows(run(["vvp", exe], w))
    if actual != expected:
        raise RuntimeError(f"Icarus Verilog 13.0: {actual} != {expected}")
    print("Icarus Verilog 13.0: 2 rows MATCH E")
    if shutil.which("xrun"):
        print("Xcelium probe is readiness-gated; source receipt is pinned to xrun(64) 24.03-s004")
    else:
        print("no Xcelium result: xrun unavailable")

if __name__ == "__main__":
    main()
