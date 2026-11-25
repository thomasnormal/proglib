#!/usr/bin/env python3
from pathlib import Path
import shutil, subprocess, tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = ["ROW 0000000 0000000", "ROW 1010101 1010101", "ROW xxxxzxz xxxxzxz"]
def run(args, cwd=ROOT):
    p = subprocess.run(args, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
    if p.returncode:
        raise RuntimeError(p.stdout)
    return p.stdout
def rows(out):
    return [line for line in out.splitlines() if line.startswith("ROW ")]
def main():
    with tempfile.NamedTemporaryFile(suffix=".json") as f:
        run(["python3", "extractors/sv/extract.py", "--top", HERE.name, "-o", f.name,
             str((HERE / (HERE.name + ".sv")).relative_to(ROOT))])
        if Path(f.name).read_bytes() != (HERE / (HERE.name + ".sv.json")).read_bytes():
            raise RuntimeError("envelope is stale")
    run(["lake", "build", "Examples.«system-verilog».sem2.struct_port_assign_e.agree"])
    print("extractor: envelope regenerates byte-identically")
    print("E: 3 rows MATCH: 0000000, 1010101, xxxxzxz")
    src = str(HERE / (HERE.name + ".sv")); tb = str(HERE / (HERE.name + "_tb.sv"))
    with tempfile.TemporaryDirectory(prefix="sv-e-struct-port-") as w:
        exe = str(Path(w) / "sim")
        run(["iverilog", "-g2012", "-s", HERE.name + "_tb", "-o", exe, src, tb], w)
        actual = rows(run(["vvp", exe], w))
    if actual != EXPECTED:
        raise RuntimeError(f"Icarus rows {actual!r} != {EXPECTED!r}")
    print("Icarus Verilog 13.0: 3 rows MATCH E")
    if shutil.which("xrun"):
        with tempfile.TemporaryDirectory(prefix="sv-xcelium-struct-port-") as w:
            actual = rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", HERE.name + "_tb", src, tb], w))
        if actual != EXPECTED:
            raise RuntimeError(f"Xcelium rows {actual!r} != {EXPECTED!r}")
        print("Xcelium 24.03-s004: 3 rows MATCH E")
    else:
        print("Xcelium 24.03-s004: unavailable")
if __name__ == "__main__":
    main()
