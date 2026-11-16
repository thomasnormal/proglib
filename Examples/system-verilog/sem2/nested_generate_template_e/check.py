#!/usr/bin/env python3
"""Receipt for nested generate template selection."""
from pathlib import Path
import shutil, subprocess, tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
def run(cmd, cwd=ROOT):
    p = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
    if p.returncode: raise RuntimeError(p.stdout)
    return p.stdout
def rows(text): return [line.split()[1:] for line in text.splitlines() if line.startswith("ROW ")]
def main():
    source = HERE / "nested_generate_template_e.sv"
    with tempfile.NamedTemporaryFile(suffix=".json") as f:
        run(["python3", "extractors/sv/extract.py", "--top", "nested_generate_template_e", "-o", f.name, str(source.relative_to(ROOT))])
        if Path(f.name).read_bytes() != (HERE / (source.name + ".json")).read_bytes(): raise RuntimeError("stale envelope")
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    print("extractor: envelope regenerates byte-identically")
    print("E: nested generate admits the selected live template; no runtime row claimed because y[0] is undriven")
    tb = HERE / "nested_generate_template_e_tb.sv"
    expected = [["y=1z"]]
    for sim in ["iverilog"] + (["xrun"] if shutil.which("xrun") else []):
        with tempfile.TemporaryDirectory(prefix="sv-nested-template-") as w:
            if sim == "iverilog":
                exe = str(Path(w) / "sim")
                run(["iverilog", "-g2012", "-s", "nested_generate_template_e_tb", "-o", exe, str(source), str(tb)], w)
                out = run(["vvp", exe], w)
            else:
                out = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "nested_generate_template_e_tb", str(source), str(tb)], w)
        if rows(out) != expected: raise RuntimeError(f"{sim}: {rows(out)} != {expected}")
        print(f"{sim}: 1 source row MATCH E")
if __name__ == "__main__": main()
