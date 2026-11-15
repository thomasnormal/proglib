#!/usr/bin/env python3
from pathlib import Path
import shutil, subprocess, tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
def run(cmd, cwd=ROOT):
    p = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=120)
    if p.returncode: raise RuntimeError(p.stdout)
    return p.stdout
def rows(text): return [line.split()[1:] for line in text.splitlines() if line.startswith("ROW ")]
def main():
    with tempfile.NamedTemporaryFile(suffix=".json") as f:
        run(["python3", "extractors/sv/extract.py", "--top", "hierarchy_indexed_canonical_e", "-o", f.name, str((HERE / "hierarchy_indexed_canonical_e.sv").relative_to(ROOT))])
        if Path(f.name).read_bytes() != (HERE / "hierarchy_indexed_canonical_e.sv.json").read_bytes(): raise RuntimeError("stale envelope")
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    expected=[["y=00000000"],["y=00000001"],["y=10100101"],["y=11110000"],["y=xxxxxxxx"]]
    print("extractor: envelope regenerates byte-identically")
    print("E: 5 indexed packed-port hierarchy rows MATCH")
    src=str(HERE/"hierarchy_indexed_canonical_e.sv"); tb=str(HERE/"hierarchy_indexed_canonical_e_tb.sv")
    with tempfile.TemporaryDirectory(prefix="sv-hierarchy-indexed-iverilog-") as w:
        exe=str(Path(w)/"sim"); run(["iverilog","-g2012","-s","hierarchy_indexed_canonical_e_tb","-o",exe,src,tb],w); actual=rows(run(["vvp",exe],w))
    if actual!=expected: raise RuntimeError(f"Icarus Verilog 13.0: {actual} != {expected}")
    print("Icarus Verilog 13.0: 5 rows MATCH E")
    if shutil.which("xrun"):
        with tempfile.TemporaryDirectory(prefix="sv-hierarchy-indexed-xcelium-") as w:
            actual=rows(run(["xrun","-sv","-q","-timescale","1ns/1ps","-top","hierarchy_indexed_canonical_e_tb",src,tb],w))
        if actual!=expected: raise RuntimeError(f"Xcelium 24.03-s004: {actual} != {expected}")
        print("Xcelium 24.03-s004: 5 rows MATCH E")
    else: print("no Xcelium result: xrun unavailable")
if __name__ == "__main__": main()
