#!/usr/bin/env python3
"""Receipt for unsigned negative $clog2 in a generate guard."""
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [["N=-1", "y=1"], ["N=0", "y=0"]]


def run(cmd, cwd=ROOT):
    p = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=180)
    if p.returncode:
        raise RuntimeError(p.stdout)
    return p.stdout


def rows(text):
    return [line.split()[1:] for line in text.splitlines()
            if line.startswith("ROW ")]


def main():
    with tempfile.NamedTemporaryFile(suffix=".json") as f:
        run(["python3", "extractors/sv/extract.py", "--top",
             "clog2_guard_negative_e", "-o", f.name,
             str((HERE / "clog2_guard_negative_e.sv").relative_to(ROOT))])
        if Path(f.name).read_bytes() != (HERE / "clog2_guard_negative_e.sv.json").read_bytes():
            raise RuntimeError("stale envelope")
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    print("extractor: envelope regenerates byte-identically")
    print("E: 2 generate-guard rows MATCH: N=-1 -> y=1, N=0 -> y=0")
    source = str(HERE / "clog2_guard_negative_e.sv")
    tb = str(HERE / "clog2_guard_negative_e_tb.sv")
    with tempfile.TemporaryDirectory(prefix="sv-e-clog2-guard-negative-") as work:
        exe = str(Path(work) / "sim")
        run(["iverilog", "-g2012", "-s", "clog2_guard_negative_e_tb",
             "-o", exe, source, tb], work)
        actual = rows(run(["vvp", exe], work))
    if actual != EXPECTED:
        raise RuntimeError(f"Icarus Verilog 13.0: {actual} != {EXPECTED}")
    print("Icarus Verilog 13.0: 2 rows MATCH E")
    if shutil.which("xrun"):
        with tempfile.TemporaryDirectory(prefix="sv-xcelium-clog2-guard-negative-") as work:
            actual = rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                               "-top", "clog2_guard_negative_e_tb", source, tb], work))
        if actual != EXPECTED:
            raise RuntimeError(f"Xcelium 24.03-s004: {actual} != {EXPECTED}")
        print("Xcelium 24.03-s004: 2 rows MATCH E")
    else:
        print("no Xcelium result: xrun unavailable")


if __name__ == "__main__":
    main()
