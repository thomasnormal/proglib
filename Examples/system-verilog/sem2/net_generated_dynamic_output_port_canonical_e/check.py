#!/usr/bin/env python3
from pathlib import Path
import os, signal, subprocess, tempfile
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
    print("E: 4 generated dynamic-output-net rows MATCH")
    with tempfile.TemporaryDirectory(prefix="sv-e-net-generated-dynamic-") as w:
        exe = str(Path(w) / "sim")
        src = str(HERE / "net_generated_dynamic_output_port_canonical_e.sv")
        tb = str(HERE / "net_generated_dynamic_output_port_canonical_e_tb.sv")
        run(["iverilog", "-g2012", "-s", "net_generated_dynamic_output_port_canonical_e_tb", "-o", exe, src, tb], w)
        actual = rows(run(["vvp", exe], w))
    expected = [["i=0", "wready_o=1"], ["i=1", "wready_o=0"], ["i=2", "wready_o=0"], ["i=3", "wready_o=0"]]
    if actual != expected: raise RuntimeError(f"Icarus Verilog 13.0: {actual} != {expected}")
    print("Icarus Verilog 13.0: 4 rows MATCH E")
if __name__ == "__main__": main()
