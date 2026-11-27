#!/usr/bin/env python3
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = ["ROW 0 y=xxxxxxxx"]


def run(args, cwd):
    p = subprocess.run(args, cwd=cwd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=180)
    if p.returncode:
        raise RuntimeError(p.stdout)
    return p.stdout


def rows(output):
    return [line.strip() for line in output.splitlines()
            if line.startswith("ROW ")]


def main():
    source = HERE / "readmemh_parameter_file.sv"
    envelope = HERE / (source.name + ".json")
    with tempfile.NamedTemporaryFile(suffix=".json") as f:
        run(["python3", "extractors/sv/extract.py", "--top",
             "readmemh_parameter_file", "--retain-proc-rewrites", "-o",
             f.name, str(source.relative_to(ROOT))], ROOT)
        if Path(f.name).read_bytes() != envelope.read_bytes():
            raise RuntimeError("stale envelope")
    run(["lake", "env", "lean", str(HERE / "agree.lean")], ROOT)
    print("extractor: envelope regenerates byte-identically")
    print("E: missing parameter-selected file leaves y=x row MATCH")
    with tempfile.TemporaryDirectory(prefix="sv-readmemh-parameter-") as w:
        w = Path(w)
        exe = w / "sim"
        run(["iverilog", "-g2012", "-s", "tb", "-o", str(exe),
             str(source), str(HERE / "readmemh_parameter_file_tb.sv")], w)
        actual = rows(run(["vvp", str(exe)], w))
    if actual != EXPECTED:
        raise RuntimeError(f"Icarus Verilog 13.0: {actual} != {EXPECTED}")
    print("Icarus Verilog 13.0: 1 row MATCH")
    if shutil.which("xrun"):
        with tempfile.TemporaryDirectory(prefix="sv-readmemh-parameter-xcelium-") as w:
            actual = rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                               "-top", "tb", str(source),
                               str(HERE / "readmemh_parameter_file_tb.sv")], w))
        if actual != EXPECTED:
            raise RuntimeError(f"Xcelium 24.03-s004: {actual} != {EXPECTED}")
        print("Xcelium 24.03-s004: 1 row MATCH")


if __name__ == "__main__":
    main()
