#!/usr/bin/env python3
"""Receipt for the assertion-only initial-process adapter."""
from pathlib import Path
import shutil
import subprocess
import tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]

def run(cmd, cwd=ROOT, check=True):
    p = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=180)
    if check and p.returncode: raise RuntimeError(p.stdout)
    return p

def rows(text):
    return [line.split()[1:] for line in text.splitlines() if line.startswith("ROW ")]

def tb(n):
    return f'''`timescale 1ns/1ps
module tb; wire y;
  initial begin
    #1 $display("ROW %b", y); #1 $display("ROW %b", y);
    #1 $display("ROW %b", y); #1 $display("ROW %b", y);
    #1 $display("ROW %b", y); #1 $display("ROW %b", y);
    #1 $display("ROW %b", y); #1 $display("ROW %b", y); $finish;
  end
  initial_parameter_check #(.N({n})) dut(.y(y));
endmodule
'''

def main():
    envelope = HERE / "initial_parameter_check_e.sv.json"
    with tempfile.NamedTemporaryFile(suffix=".json") as f:
        p = run(["python3", "extractors/sv/extract.py", "--top", "initial_parameter_check",
                 "-o", f.name, str((HERE / "initial_parameter_check_e.sv").relative_to(ROOT))])
        if Path(f.name).read_bytes() != envelope.read_bytes(): raise RuntimeError("stale envelope")
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    print("extractor: envelope regenerates byte-identically")
    for n in (1, 0):
        expected = [["1"]] * 8 if n else [["0"]] * 8
        for sim in ["iverilog"] + (["xrun"] if shutil.which("xrun") else []):
            with tempfile.TemporaryDirectory(prefix=f"sv-initial-check-{n}-") as work:
                work = Path(work); source = HERE / "initial_parameter_check_e.sv"; tb_path = work / "tb.sv"
                tb_path.write_text(tb(n))
                if sim == "iverilog":
                    exe = str(work / "sim")
                    out = run(["iverilog", "-g2012", "-s", "tb", "-o", exe, str(source), str(tb_path)], work)
                    out = run(["vvp", exe], work).stdout
                else:
                    proc = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "tb", str(source), str(tb_path)], work, check=(n != 0))
                    out = proc.stdout
                if rows(out) != expected: raise RuntimeError(f"{sim} N={n}: {rows(out)} != {expected}")
                if sim == "xrun" and n == 0 and "ASRTST" not in out: raise RuntimeError("missing expected ASRTST")
            print(f"{sim} N={n}: 8 source rows MATCH")
if __name__ == "__main__": main()
