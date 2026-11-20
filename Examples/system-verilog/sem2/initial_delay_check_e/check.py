#!/usr/bin/env python3
"""Receipt for the diagnostic-only initial delay adapter."""
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]


def run(cmd, cwd=ROOT, check=True):
    p = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=180)
    if check and p.returncode:
        raise RuntimeError(p.stdout)
    return p


def rows(text):
    return [line.split()[1:] for line in text.splitlines() if line.startswith("ROW ")]


def main():
    envelope = HERE / "initial_delay_check_e.sv.json"
    with tempfile.NamedTemporaryFile(suffix=".json") as f:
        run(["python3", "extractors/sv/extract.py", "--top", "initial_delay_check",
             "-o", f.name, str((HERE / "initial_delay_check_e.sv").relative_to(ROOT))])
        if Path(f.name).read_bytes() != envelope.read_bytes():
            raise RuntimeError("stale envelope")
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    tb = '''`timescale 1ns/1ps
module tb; logic x; wire y;
  initial begin
    x = 1'bx; #1 $display("ROW %b", y);
    x = 1'b0; #1 $display("ROW %b", y);
    x = 1'b1; #1 $display("ROW %b", y);
    x = 1'bz; #1 $display("ROW %b", y); $finish;
  end
  initial_delay_check dut(.x(x), .y(y));
endmodule
'''
    expected = [["x"], ["0"], ["1"], ["z"]]
    for sim in ["iverilog"] + (["xrun"] if shutil.which("xrun") else []):
        with tempfile.TemporaryDirectory(prefix="sv-initial-delay-") as td:
            work = Path(td)
            tb_path = work / "tb.sv"
            tb_path.write_text(tb)
            if sim == "iverilog":
                exe = work / "sim"
                run(["iverilog", "-g2012", "-s", "tb", "-o", str(exe),
                     str(HERE / "initial_delay_check_e.sv"), str(tb_path)], work)
                out = run(["vvp", str(exe)], work).stdout
            else:
                out = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "tb",
                           str(HERE / "initial_delay_check_e.sv"), str(tb_path)], work).stdout
            if rows(out) != expected:
                raise RuntimeError(f"{sim}: {rows(out)} != {expected}")
        print(f"{sim}: 4 source rows MATCH")
    print("ordinary receipt: diagnostic-only initial delay")


if __name__ == "__main__":
    main()
