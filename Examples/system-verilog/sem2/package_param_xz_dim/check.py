#!/usr/bin/env python3
from pathlib import Path
import shutil, subprocess, tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SRC = HERE / "package_param_xz_dim.sv"
ENV = HERE / "package_param_xz_dim.sv.json"
TB = HERE / "package_param_xz_dim_tb.sv"

def run(cmd, cwd=ROOT):
    return subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, timeout=120)

def main():
    with tempfile.NamedTemporaryFile(suffix=".json") as f:
        p = run(["python3", "extractors/sv/extract.py", "--top", "m", "-o", f.name,
                 str(SRC.relative_to(ROOT))])
        if p.returncode or Path(f.name).read_bytes() != ENV.read_bytes():
            raise RuntimeError("stale envelope\n" + p.stdout)
    p = run(["lake", "env", "lean", str(HERE / "agree.lean")])
    if p.returncode:
        raise RuntimeError(p.stdout)
    print("E: named refusal for x/z package parameter in packed dimension")
    with tempfile.TemporaryDirectory(prefix="sv-package-xz-dim-") as w:
        exe = str(Path(w) / "sim")
        p = run(["iverilog", "-g2012", "-s", "tb", "-o", exe, str(SRC), str(TB)], w)
        if p.returncode:
            raise RuntimeError(p.stdout)
        out = run(["vvp", exe], w).stdout
    if "ROW 0" not in out:
        raise RuntimeError(out)
    print("Icarus Verilog 13.0: 1 source row retained")
    if shutil.which("xrun"):
        print("Xcelium 24.03-s004: source row requires external license receipt")
    else:
        print("no Xcelium result: xrun unavailable")

if __name__ == "__main__":
    main()
