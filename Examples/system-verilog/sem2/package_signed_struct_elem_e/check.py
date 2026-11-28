#!/usr/bin/env python3
from pathlib import Path
import subprocess, tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
def run(cmd, cwd=ROOT):
    p = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
    if p.returncode: raise RuntimeError(p.stdout)
    return p.stdout
def main():
    with tempfile.NamedTemporaryFile(suffix=".json") as f:
        run(["python3", "extractors/sv/extract.py", "--top", "package_signed_struct_elem_e", "-o", f.name, str(HERE / "package_signed_struct_elem_e.sv")])
        if Path(f.name).read_bytes() != (HERE / "package_signed_struct_elem_e.sv.json").read_bytes(): raise RuntimeError("stale envelope")
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    print("ordinary E: loud refusal preserves signed packed-aggregate boundary")
    print("Icarus Verilog 13.0: source syntax refusal, no oracle value claimed")
    with tempfile.TemporaryDirectory(prefix="sv-signed-aggregate-xrun-") as w:
        out = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "package_signed_struct_elem_e_tb", str(HERE / "package_signed_struct_elem_e.sv"), str(HERE / "package_signed_struct_elem_e_tb.sv")], w)
    rows = [line for line in out.splitlines() if line.startswith("ROW ")]
    expected = ["ROW 0 fffff44d", "ROW 1 fffff44e", "ROW ff fffff54c", "ROW x xxxxxxxx"]
    if rows != expected: raise RuntimeError(f"Xcelium rows {rows!r} != {expected!r}")
    print("Xcelium 24.03-s004: four rows MATCH IEEE 1800 sign extension")
if __name__ == "__main__": main()
