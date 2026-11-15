#!/usr/bin/env python3
from pathlib import Path
import shutil
import subprocess, tempfile
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
        run(["python3", "extractors/sv/extract.py", "--top", "bits_package_parameter_e",
             "-o", f.name, str((HERE / "bits_package_parameter_e.sv").relative_to(ROOT))])
        if Path(f.name).read_bytes() != (HERE / "bits_package_parameter_e.sv.json").read_bytes():
            raise RuntimeError("stale envelope")
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    print("extractor: envelope regenerates byte-identically")
    print("E: 1 $bits(package-parameter) row MATCH: y=00001000")
    expected = [["y=00001000"]]
    tb = HERE / "bits_package_parameter_e_tb.sv"
    with tempfile.TemporaryDirectory(prefix="sv-e-bits-package-") as w:
        exe = str(Path(w) / "sim")
        run(["iverilog", "-g2012", "-s", "bits_package_parameter_e_tb", "-o", exe,
             str(HERE / "bits_package_parameter_e.sv"), str(tb)], w)
        actual = rows(run(["vvp", exe], w))
    if actual != expected:
        raise RuntimeError(f"Icarus Verilog 13.0: {actual} != {expected}")
    print("Icarus Verilog 13.0: 1 row MATCH E")
    if shutil.which("xrun"):
        with tempfile.TemporaryDirectory(prefix="sv-xcelium-bits-package-") as w:
            actual = rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top",
                               "bits_package_parameter_e_tb",
                               str(HERE / "bits_package_parameter_e.sv"), str(tb)], w))
        if actual != expected:
            raise RuntimeError(f"Xcelium 24.03-s004: {actual} != {expected}")
        print("Xcelium 24.03-s004: 1 row MATCH E")
    else:
        print("no Xcelium result: xrun unavailable")
if __name__ == "__main__":
    main()
