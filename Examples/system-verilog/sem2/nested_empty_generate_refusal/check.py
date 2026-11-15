#!/usr/bin/env python3
from pathlib import Path
import shutil, subprocess, tempfile
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
        run(["python3", "extractors/sv/extract.py", "--top", "nested_empty_generate_refusal",
             "-o", f.name, str((HERE / "nested_empty_generate_refusal.sv").relative_to(ROOT))])
        generated = Path(f.name).read_bytes()
    checked = (HERE / "nested_empty_generate_refusal.sv.json").read_bytes()
    if generated != checked:
        raise RuntimeError("stale envelope")
    text = checked.decode()
    marker = '"sv_kind": "GenerateFor:no-template"'
    if marker not in text:
        raise RuntimeError("expected GenerateFor:no-template refusal is absent")
    print("extractor: envelope regenerates byte-identically")
    print("E ordinary route: REFUSED GenerateFor:no-template; no E row claimed")
    expected = [["y=1z"]]
    src = str(HERE / "nested_empty_generate_refusal.sv")
    tb = str(HERE / "nested_empty_generate_refusal_tb.sv")
    with tempfile.TemporaryDirectory(prefix="sv-nested-empty-iverilog-") as w:
        exe = str(Path(w) / "sim")
        run(["iverilog", "-g2012", "-s", "nested_empty_generate_refusal_tb", "-o", exe, src, tb], w)
        actual = rows(run(["vvp", exe], w))
    if actual != expected:
        raise RuntimeError(f"Icarus Verilog 13.0: {actual} != {expected}")
    print("Icarus Verilog 13.0: source row y=1z")
    if shutil.which("xrun"):
        with tempfile.TemporaryDirectory(prefix="sv-nested-empty-xcelium-") as w:
            actual = rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top",
                               "nested_empty_generate_refusal_tb", src, tb], w))
        if actual != expected:
            raise RuntimeError(f"Xcelium 24.03-s004: {actual} != {expected}")
        print("Xcelium 24.03-s004: source row y=1z")
    else:
        print("no Xcelium result: xrun unavailable")
if __name__ == "__main__":
    main()
