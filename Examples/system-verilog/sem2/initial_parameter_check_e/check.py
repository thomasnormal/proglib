#!/usr/bin/env python3
"""Receipt for the assertion-only initial-process adapter."""
from pathlib import Path
import subprocess
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
def run(cmd):
    p = subprocess.run(cmd, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=180)
    if p.returncode: raise RuntimeError(p.stdout)
    return p.stdout
def main():
    run(["python3", "extractors/sv/extract.py", "--top", "initial_parameter_check",
         "-o", "/tmp/initial_parameter_check_e.json",
         str((HERE / "initial_parameter_check_e.sv").relative_to(ROOT))])
    if Path("/tmp/initial_parameter_check_e.json").read_bytes() != (HERE / "initial_parameter_check_e.sv.json").read_bytes():
        raise RuntimeError("stale envelope")
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    print("extractor: envelope regenerates byte-identically")
    out = run(["python3", "harness/sv/batch_receipt.py", "--cleanroom-dir", "/var/tmp/thomas-ahle/fleet2/cleanroom", "--only", "initial_parameter_check", "--ordinary-timeout", "180"])
    if "N1" not in out or "N0" not in out or "MATCH E" not in out:
        raise RuntimeError(out)
    print("Icarus Verilog 13.0 and Xcelium 24.03-s004: 16 source rows MATCH E")
if __name__ == "__main__": main()
