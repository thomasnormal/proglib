#!/usr/bin/env python3
"""Receipt for signed/width conversion in constant-derived runtime logic."""
from pathlib import Path
import shutil, subprocess, tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [["x=0", "y8=0", "y4=0"], ["x=1", "y8=1", "y4=1"],
            ["x=x", "y8=x", "y4=x"], ["x=z", "y8=x", "y4=x"]]
def run(cmd, cwd=ROOT):
    p = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=180)
    if p.returncode: raise RuntimeError(p.stdout)
    return p.stdout
def rows(text): return [line.split()[1:] for line in text.splitlines() if line.startswith("ROW ")]
def main():
    source = HERE / "constant_width_conversion_e.sv"
    with tempfile.NamedTemporaryFile(suffix=".json") as f:
        run(["python3", "extractors/sv/extract.py", "--top", "constant_width_conversion_e",
             "-o", f.name, str(source.relative_to(ROOT))])
        if Path(f.name).read_bytes() != (HERE / (source.name + ".json")).read_bytes():
            raise RuntimeError("stale envelope")
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    print("extractor: envelope regenerates byte-identically")
    print("E: E=8 and E=4, 8 width-conversion rows MATCH")
    tb = HERE / "constant_width_conversion_e_tb.sv"
    for sim in ["iverilog"] + (["xrun"] if shutil.which("xrun") else []):
        with tempfile.TemporaryDirectory(prefix="sv-width-conversion-") as w:
            if sim == "iverilog":
                exe = str(Path(w) / "sim")
                run(["iverilog", "-g2012", "-s", "constant_width_conversion_e_tb", "-o", exe, str(source), str(tb)], w)
                out = run(["vvp", exe], w)
            else:
                out = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "constant_width_conversion_e_tb", str(source), str(tb)], w)
        actual = rows(out)
        if actual != EXPECTED: raise RuntimeError(f"{sim}: {actual} != {EXPECTED}")
        print(f"{sim}: 4 source rows MATCH E")
if __name__ == "__main__": main()
