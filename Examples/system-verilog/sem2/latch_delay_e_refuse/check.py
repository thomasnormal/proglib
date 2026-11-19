#!/usr/bin/env python3
"""Differential refusal receipt for timing in an always_latch process."""
from pathlib import Path
import subprocess
import tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]

def run(cmd, cwd=ROOT, check=True):
    return subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, check=check, timeout=180).stdout

def main():
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    census = run(["python3", "harness/sv/refusal_census.py", "ordinary",
                  str(HERE / "latch_delay_e.sv.json")])
    if "SlangError:TimingInFuncNotAllowed" not in census:
        raise RuntimeError(f"missing canonical-E refusal: {census}")
    print("canonical E: EXPECTED SlangError:TimingInFuncNotAllowed refusal")
    source = HERE / "latch_delay_e.sv"
    tb = """module tb; logic en, a, q; latch_delay_e dut(.en(en), .a(a), .q(q)); initial begin en=1'b1; a=1'b0; #2 $display(\"UNREACHED\"); $finish; end endmodule\n"""
    for sim in ("iverilog", "xrun"):
        with tempfile.TemporaryDirectory(prefix=f"sv-latch-delay-{sim}-") as work:
            work = Path(work)
            tb_path = work / "tb.sv"
            tb_path.write_text(tb)
            if sim == "iverilog":
                proc = subprocess.run(["iverilog", "-g2012", "-s", "tb", "-o", str(work / "sim"),
                                       str(source), str(tb_path)], cwd=work,
                                      text=True, stdout=subprocess.PIPE,
                                      stderr=subprocess.STDOUT, check=False, timeout=180)
                output = proc.stdout
            else:
                proc = subprocess.run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "tb",
                                       str(source), str(tb_path)], cwd=work,
                                      text=True, stdout=subprocess.PIPE,
                                      stderr=subprocess.STDOUT, check=False, timeout=180)
                output = proc.stdout
            if proc.returncode == 0:
                raise RuntimeError(f"{sim} unexpectedly accepted timing control:\n{output}")
            print(f"{sim}: EXPECTED SOURCE REFUSAL")
            if sim == "iverilog" and "blocking delay" not in output:
                raise RuntimeError(f"Icarus diagnostic missing always_latch delay text:\n{output}")
            if sim == "xrun" and "DLYSYN" not in output:
                raise RuntimeError(f"Xcelium diagnostic missing DLYSYN:\n{output}")

if __name__ == "__main__":
    main()
