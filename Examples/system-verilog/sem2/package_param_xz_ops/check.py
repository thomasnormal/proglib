#!/usr/bin/env python3
"""Differential receipt for four-state package-parameter operands."""
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SRC = HERE / "package_param_xz_ops.sv"
ENV = HERE / "package_param_xz_ops.sv.json"
TB = HERE / "package_param_xz_ops_tb.sv"

def run(cmd, cwd=ROOT):
    return subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, timeout=120)

def rows(text):
    return [line.split()[1:] for line in text.splitlines() if line.startswith("ROW ")]

def main():
    with tempfile.NamedTemporaryFile(suffix=".json") as f:
        p = run(["python3", "extractors/sv/extract.py", "--top", "package_param_xz_ops",
                 "-o", f.name, str(SRC.relative_to(ROOT))])
        if p.returncode or Path(f.name).read_bytes() != ENV.read_bytes():
            raise RuntimeError("envelope regeneration failed or is stale\n" + p.stdout)
    p = run(["lake", "env", "lean", str(HERE / "agree.lean")])
    if p.returncode:
        raise RuntimeError(p.stdout)
    print("extractor and Lean four-state receipt: MATCH")
    expected = [["1101", "1", "1", "0"], ["1111", "0", "0", "0"],
                ["1z0z", "1", "1", "1"]]
    # Icarus 13.0 does not parse case-inside. Compile the faithful source with
    # that unsupported construct disabled and record the source limitation.
    with tempfile.TemporaryDirectory(prefix="sv-package-xz-ops-icarus-") as w:
        exe = str(Path(w) / "sim")
        p = run(["iverilog", "-g2012", "-DNO_INSIDE", "-s", "package_param_xz_ops_tb",
                 "-o", exe, str(SRC), str(TB)], w)
        if p.returncode:
            raise RuntimeError("Icarus rejected the reduced source:\n" + p.stdout)
        actual = rows(run(["vvp", exe], w).stdout)
    expected_icarus = [["1101", "1", "0", "0"], ["1111", "0", "0", "0"],
                       ["1z0z", "1", "0", "1"]]
    if actual != expected_icarus:
        raise RuntimeError(f"Icarus reduced-source rows: {actual} != {expected_icarus}")
    print("Icarus Verilog 13.0: 3 rows MATCH for casez/===, inside is parser-limited")
    if shutil.which("xrun"):
        with tempfile.TemporaryDirectory(prefix="sv-package-xz-ops-xcelium-") as w:
            p = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top",
                     "package_param_xz_ops_tb", str(SRC), str(TB)], w)
            if p.returncode:
                raise RuntimeError("Xcelium rejected the faithful source:\n" + p.stdout)
            actual = rows(p.stdout)
        if actual != expected:
            raise RuntimeError(f"Xcelium rows: {actual} != {expected}")
        print("Xcelium 24.03-s004: 3 rows MATCH")
    else:
        print("no Xcelium result: xrun unavailable")

if __name__ == "__main__":
    main()
