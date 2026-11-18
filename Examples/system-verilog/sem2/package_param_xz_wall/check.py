#!/usr/bin/env python3
"""Differential receipt for a four-state package parameter default."""
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SRC = HERE / "package_param_xz_wall.sv"
ENV = HERE / "package_param_xz_wall.sv.json"
TB = HERE / "package_param_xz_wall_tb.sv"

def run(cmd, cwd=ROOT):
    p = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=120)
    return p

def rows(text):
    return [line.split()[1:] for line in text.splitlines() if line.startswith("ROW ")]

def main():
    with tempfile.NamedTemporaryFile(suffix=".json") as f:
        p = run(["python3", "extractors/sv/extract.py", "--top",
                 "package_param_xz_wall", "-o", f.name, str(SRC.relative_to(ROOT))])
        if p.returncode:
            raise RuntimeError(p.stdout)
        if Path(f.name).read_bytes() != ENV.read_bytes():
            raise RuntimeError("stale envelope")
    p = run(["lake", "env", "lean", str(HERE / "agree.lean")])
    if p.returncode:
        raise RuntimeError(p.stdout)
    print("extractor: envelope regenerates byte-identically")
    expected = [["z" * 25 + "0110111"]]
    with tempfile.TemporaryDirectory(prefix="sv-package-xz-icarus-") as w:
        exe = str(Path(w) / "sim")
        p = run(["iverilog", "-g2012", "-s", "package_param_xz_wall_tb",
                 "-o", exe, str(SRC), str(TB)], w)
        if p.returncode:
            raise RuntimeError("Icarus Verilog 13.0 refused the faithful source:\n" + p.stdout)
        actual = rows(run(["vvp", exe], w).stdout)
    if actual != expected:
        raise RuntimeError(f"Icarus Verilog 13.0: {actual} != {expected}")
    print("Icarus Verilog 13.0: 1 row MATCH source")
    if shutil.which("xrun"):
        with tempfile.TemporaryDirectory(prefix="sv-package-xz-xcelium-") as w:
            p = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top",
                     "package_param_xz_wall_tb", str(SRC), str(TB)], w)
            if p.returncode:
                raise RuntimeError("Xcelium 24.03-s004 refused the faithful source:\n" + p.stdout)
            actual = rows(p.stdout)
        if actual != expected:
            raise RuntimeError(f"Xcelium 24.03-s004: {actual} != {expected}")
        print("Xcelium 24.03-s004: 1 row MATCH source")
    else:
        print("no Xcelium result: xrun unavailable")
    print("E: loud refusal at package x/z constant elaboration")

if __name__ == "__main__":
    main()
