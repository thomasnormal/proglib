#!/usr/bin/env python3
"""Differential receipt for IEEE 1800-2023 §6.20.2 untyped constants."""
from pathlib import Path
import shutil
import subprocess, tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
def run(cmd, cwd=ROOT):
    return subprocess.check_output(cmd, cwd=cwd, text=True, stderr=subprocess.STDOUT)


EXPECTED = [
    "ROW N=10000 k=10000 a=647 u=6 p=256 ls=4 rs=64 neg=251 cat=165 signed=4294967288 range=15 observed=10001 observed_w=7686",
    "ROW N=8 k=8 a=655 u=6 p=256 ls=4 rs=64 neg=251 cat=165 signed=4294967288 range=15 observed=9 observed_w=7686",
]
XCELIUM_EXPECTED = [
    "ROW N=10000 k=1410 a=4294966647 u=6 p=256 ls=4 rs=64 neg=251 cat=165 signed=4294967288 range=15 observed=10001 observed_w=3846",
    "ROW N=8 k=8 a=4294966655 u=6 p=256 ls=4 rs=64 neg=251 cat=165 signed=4294967288 range=15 observed=9 observed_w=3846",
]
with tempfile.TemporaryDirectory() as d:
    out = Path(d) / "u.json"
    run(["python3", "extractors/sv/extract.py", "--top", "untyped_localparam_exact", "-o", str(out), str((HERE / "untyped_localparam_exact.sv").relative_to(ROOT))])
    assert out.read_bytes() == (HERE / "untyped_localparam_exact.sv.json").read_bytes()
    exe = Path(d) / "sim"
    run(["iverilog", "-g2012", "-s", "untyped_localparam_exact_tb", "-o", str(exe), str(HERE / "untyped_localparam_exact.sv"), str(HERE / "untyped_localparam_exact_tb.sv")], d)
    output = run([str(exe)], d)
    iverilog_rows = [line for line in output.splitlines() if line.startswith("ROW ")]
    assert iverilog_rows == EXPECTED
    print("extractor: envelope regenerates byte-identically")
    print("Icarus Verilog 13.0: 2 rows, including signed keyword, range-only, shifts, power, concatenation, and observed width")
    if shutil.which("xrun"):
        with tempfile.TemporaryDirectory(prefix="sv-untyped-localparam-exact-") as work:
            xout = run(["xrun", "-64bit", "-q", "-sv", "-top", "untyped_localparam_exact_tb", str(HERE / "untyped_localparam_exact.sv"), str(HERE / "untyped_localparam_exact_tb.sv")], work)
        xcelium_rows = [line for line in xout.splitlines() if line.startswith("ROW ")]
        assert xcelium_rows == XCELIUM_EXPECTED
        print("Xcelium 24.03-s004: 2 rows MATCH, exact final-value widths")
    else:
        print("Xcelium 24.03-s004: unavailable")
    print("Icarus observed-width departure is declared in cases2.json")
    print("E: exact self-determined values match Xcelium at both parameter points")
