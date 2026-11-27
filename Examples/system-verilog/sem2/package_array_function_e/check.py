#!/usr/bin/env python3
from pathlib import Path
import shutil, subprocess, tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [["0", "07"], ["ff", "06"], ["x", "xx"], ["z", "xx"]]
def run(cmd, cwd=ROOT):
    p = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
    if p.returncode: raise RuntimeError(p.stdout)
    return p.stdout
def rows(s): return [line.split()[1:] for line in s.splitlines() if line.startswith("ROW ")]
def main():
    source = HERE / "package_array_function_e.sv"
    envelope = HERE / (source.name + ".json")
    with tempfile.NamedTemporaryFile(suffix=".json") as f:
        run(["python3", "extractors/sv/extract.py", "--top", "package_array_function_e", "-o", f.name, str(source)])
        if Path(f.name).read_bytes() != envelope.read_bytes(): raise RuntimeError("stale envelope")
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    print("extractor: envelope regenerates byte-identically")
    print("E: four package-array constant-function rows MATCH")
    tb = HERE / "package_array_function_e_tb.sv"
    if shutil.which("iverilog"):
        with tempfile.TemporaryDirectory(prefix="sv-package-array-function-iverilog-") as w:
            p = subprocess.run(["iverilog", "-g2012", "-s", "package_array_function_e_tb",
                                "-o", str(Path(w) / "sim"), str(source), str(tb)],
                               cwd=w, text=True, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, timeout=180)
        if p.returncode == 0:
            raise RuntimeError("Icarus unexpectedly accepted unpacked package-array parameter syntax")
        print("Icarus Verilog 13.0: source syntax refused, no oracle result claimed")
    for sim in (["xrun"] if shutil.which("xrun") else []):
        with tempfile.TemporaryDirectory(prefix="sv-package-array-function-") as w:
            if sim == "iverilog":
                exe = str(Path(w) / "sim")
                run(["iverilog", "-g2012", "-s", "package_array_function_e_tb", "-o", exe, str(source), str(tb)], w)
                out = run(["vvp", exe], w)
            else:
                out = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "package_array_function_e_tb", str(source), str(tb)], w)
        if rows(out) != EXPECTED: raise RuntimeError(f"{sim}: {rows(out)} != {EXPECTED}")
        print(f"{sim}: four source rows MATCH")
if __name__ == "__main__": main()
