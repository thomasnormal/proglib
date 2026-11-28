#!/usr/bin/env python3
from pathlib import Path
import subprocess, tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = ["ROW 0 ??01", "ROW 1 0201", "ROW 2 0210", "ROW 3 1110", "ROW 4 11ff"]
def run(cmd, cwd=ROOT):
    p = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=180)
    if p.returncode: raise RuntimeError(p.stdout)
    return p.stdout
def main():
    with tempfile.NamedTemporaryFile(suffix=".json") as f:
        run(["python3", "extractors/sv/extract.py", "--top", "mixed_array_edge_e", "-o", f.name, str(HERE / "mixed_array_edge_e.sv")])
        if Path(f.name).read_bytes() != (HERE / "mixed_array_edge_e.sv.json").read_bytes(): raise RuntimeError("stale envelope")
    out = run(["lake", "env", "lean", str(HERE / "agree.lean")])
    if "0001000100010000" not in out: raise RuntimeError("ordinary memory receipt missing corrected trace")
    print("ordinary memory route: five rows MATCH")
    for name, cmd in (("Icarus Verilog 13.0", ["iverilog", "-g2012", "-s", "mixed_array_edge_e_tb", "-o"]), ("Xcelium 24.03-s004", ["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "mixed_array_edge_e_tb"])):
        with tempfile.TemporaryDirectory(prefix="sv-mixed-array-edge-") as w:
            if name.startswith("Icarus"):
                exe = str(Path(w) / "sim")
                run(cmd + [exe, str(HERE / "mixed_array_edge_e.sv"), str(HERE / "mixed_array_edge_e_tb.sv")], w)
                got = [line for line in run(["vvp", exe], w).splitlines() if line.startswith("ROW ")]
            else:
                got = [line for line in run(cmd + ["-xmlibdirname", str(Path(w) / "xcelium.d"), str(HERE / "mixed_array_edge_e.sv"), str(HERE / "mixed_array_edge_e_tb.sv")], w).splitlines() if line.startswith("ROW ")]
        normalized = [line.replace("x", "?").replace("z", "?") for line in got]
        if normalized != EXPECTED: raise RuntimeError(f"{name}: {got!r} != {EXPECTED!r}")
        print(f"{name}: five rows MATCH")
if __name__ == "__main__": main()
