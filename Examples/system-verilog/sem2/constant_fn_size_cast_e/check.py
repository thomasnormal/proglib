#!/usr/bin/env python3
from pathlib import Path
import subprocess, tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [["0", "01"], ["ff", "00"], ["x", "xx"], ["z", "xx"]]
def run(cmd, cwd=ROOT):
    p = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
    if p.returncode:
        raise RuntimeError(p.stdout)
    return p.stdout
def rows(s):
    return [line.split()[1:] for line in s.splitlines() if line.startswith("ROW ")]
def main():
    source = HERE / "constant_fn_size_cast_e.sv"
    envelope = HERE / (source.name + ".json")
    with tempfile.NamedTemporaryFile(suffix=".json") as f:
        run(["python3", "extractors/sv/extract.py", "--top", "leaf", "-o", f.name, str(source)])
        if Path(f.name).read_bytes() != envelope.read_bytes():
            raise RuntimeError("stale envelope")
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    print("extractor: envelope regenerates byte-identically")
    print("E: four explicit-size-cast constant-function rows MATCH")
    with tempfile.TemporaryDirectory(prefix="sv-constant-fn-size-cast-iverilog-") as w:
        exe = str(Path(w) / "sim")
        run(["iverilog", "-g2012", "-s", "constant_fn_size_cast_e_tb", "-o", exe,
             str(source), str(HERE / "constant_fn_size_cast_e_tb.sv")], w)
        out = run(["vvp", exe], w)
    if rows(out) != EXPECTED:
        raise RuntimeError(f"Icarus: {rows(out)} != {EXPECTED}")
    print("Icarus Verilog 13.0: four source rows MATCH")
    if subprocess.call(["sh", "-c", "command -v xrun >/dev/null 2>&1"]) == 0:
        with tempfile.TemporaryDirectory(prefix="sv-constant-fn-size-cast-xcelium-") as w:
            out = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top",
                       "constant_fn_size_cast_e_tb", str(source),
                       str(HERE / "constant_fn_size_cast_e_tb.sv")], w)
        if rows(out) != EXPECTED:
            raise RuntimeError(f"Xcelium: {rows(out)} != {EXPECTED}")
        print("Xcelium Verilog 24.03-s004: four source rows MATCH")
if __name__ == "__main__":
    main()
