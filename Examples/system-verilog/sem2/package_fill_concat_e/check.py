#!/usr/bin/env python3
"""Differential receipt for unbased fill operands in localparam concatenations."""
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [
    ["W=4", "00001", "00010", "01", "11"],
    ["W=8", "000000001", "000000010", "01", "11"],
]


def run(cmd, cwd=ROOT):
    result = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=180)
    if result.returncode:
        raise RuntimeError(result.stdout)
    return result.stdout


def rows(text):
    return [line.split()[1:] for line in text.splitlines()
            if line.startswith("ROW ")]


def main():
    source = HERE / "package_fill_concat_e.sv"
    envelope = HERE / (source.name + ".json")
    with tempfile.NamedTemporaryFile(suffix=".json") as fresh:
        run(["python3", "extractors/sv/extract.py", "--top",
             "package_fill_concat_e", "--probe-points", "W=4;W=8",
             "-o", fresh.name, str(source.relative_to(ROOT))])
        if Path(fresh.name).read_bytes() != envelope.read_bytes():
            raise RuntimeError("stale envelope")
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    print("extractor: envelope regenerates byte-identically")
    print("E: W=4 and W=8, four output rows MATCH")
    tb = HERE / "package_fill_concat_e_tb.sv"
    for simulator in ["iverilog"] + (["xrun"] if shutil.which("xrun") else []):
        with tempfile.TemporaryDirectory(prefix="sv-package-fill-concat-") as work:
            if simulator == "iverilog":
                executable = str(Path(work) / "sim")
                run(["iverilog", "-g2012", "-s", "package_fill_concat_e_tb",
                     "-o", executable, str(source), str(tb)], work)
                output = run(["vvp", executable], work)
            else:
                output = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                              "-top", "package_fill_concat_e_tb", str(source),
                              str(tb)], work)
        actual = rows(output)
        if actual != EXPECTED:
            raise RuntimeError(f"{simulator}: {actual} != {EXPECTED}")
        print(f"{simulator}: 2 source rows MATCH")


if __name__ == "__main__":
    main()
