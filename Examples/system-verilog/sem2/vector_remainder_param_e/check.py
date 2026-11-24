#!/usr/bin/env python3
from pathlib import Path
import shutil, subprocess, tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]

def run(cmd, cwd=ROOT):
    p = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=120)
    if p.returncode:
        raise RuntimeError(p.stdout)
    return p.stdout

def rows(text):
    return [line.split()[1:] for line in text.splitlines() if line.startswith("ROW ")]

def main():
    with tempfile.NamedTemporaryFile(suffix=".json") as f:
        run(["python3", "extractors/sv/extract.py", "--top",
             "vector_remainder_param_e", "-o", f.name,
             str(HERE / "vector_remainder_param_e.sv")])
        if Path(f.name).read_bytes() != (HERE / "vector_remainder_param_e.sv.json").read_bytes():
            raise RuntimeError("stale envelope")
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    expected = [["y=00000011"]]
    print("extractor: envelope regenerates byte-identically")
    print("E: 1 vector remainder row MATCH: y=00000011")
    with tempfile.TemporaryDirectory(prefix="sv-e-vector-remainder-") as w:
        exe = str(Path(w) / "sim")
        run(["iverilog", "-g2012", "-s", "vector_remainder_param_e_tb",
             "-o", exe, str(HERE / "vector_remainder_param_e.sv"),
             str(HERE / "vector_remainder_param_e_tb.sv")], w)
        if rows(run([exe], w)) != expected:
            raise RuntimeError("Icarus Verilog 13.0 row mismatch")
    print("Icarus Verilog 13.0: 1 row MATCH E")
    if shutil.which("xrun"):
        with tempfile.TemporaryDirectory(prefix="sv-xcelium-vector-remainder-") as w:
            out = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                       "-top", "vector_remainder_param_e_tb",
                       str(HERE / "vector_remainder_param_e.sv"),
                       str(HERE / "vector_remainder_param_e_tb.sv")], w)
        if rows(out) != expected:
            raise RuntimeError("Xcelium row mismatch")
        print("Xcelium 24.03-s004: 1 row MATCH E")
    else:
        print("no Xcelium result: xrun unavailable")

if __name__ == "__main__": main()
