#!/usr/bin/env python3
"""Differential receipt for per-instance names in a direct generate-for scope."""
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCE = HERE / "w2_scope.sv"
ENVELOPE = HERE / "w2_scope.json"
EXPECTED = [
    "ROW 00 00",
    "ROW 01 01",
    "ROW 10 10",
    "ROW xz xz",
    "ROW zz zz",
]
TB = r'''module tb;
  logic [1:0] a;
  wire [1:0] q;
  w2_scope #(.N(2)) dut(.a(a), .q(q));
  initial begin
    a = 2'b00; #1 $display("ROW %b %b", a, q);
    a = 2'b01; #1 $display("ROW %b %b", a, q);
    a = 2'b10; #1 $display("ROW %b %b", a, q);
    a = 2'bxz; #1 $display("ROW %b %b", a, q);
    a = 2'bzz; #1 $display("ROW %b %b", a, q);
    $finish;
  end
endmodule
'''


def run(command, cwd=ROOT):
    result = subprocess.run(command, cwd=cwd, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            timeout=180)
    if result.returncode:
        raise RuntimeError(result.stdout)
    return result.stdout


def rows(output):
    return [line for line in output.splitlines() if line.startswith("ROW ")]


def main():
    scratch = ROOT / ".scratch"
    scratch.mkdir(exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=scratch, suffix=".json") as fresh:
        run(["python3", "extractors/sv/extract.py", "--top", "w2_scope",
             "-o", fresh.name, str(SOURCE.relative_to(ROOT))])
        if Path(fresh.name).read_bytes() != ENVELOPE.read_bytes():
            raise RuntimeError("checked-in envelope differs from Slang extraction")
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    for simulator in ["iverilog"] + (["xrun"] if shutil.which("xrun") else []):
        with tempfile.TemporaryDirectory(dir=scratch, prefix="sv-w2-scope-") as work:
            work_path = Path(work)
            tb = work_path / "tb.sv"
            tb.write_text(TB)
            if simulator == "iverilog":
                executable = work_path / "sim"
                run(["iverilog", "-g2012", "-s", "tb", "-o", str(executable),
                     str(SOURCE), str(tb)], work)
                output = run(["vvp", str(executable)], work)
                version = run(["iverilog", "-V"], work).splitlines()[0]
            else:
                output = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                              "-top", "tb", str(SOURCE), str(tb)], work)
                version = run(["xrun", "-version"], work).splitlines()[0]
        actual = rows(output)
        if actual != EXPECTED:
            raise RuntimeError(f"{simulator}: {actual!r} != {EXPECTED!r}")
        print(f"{version}: {len(actual)} rows MATCH")
    print("ordinary E: direct generate-for declaration names are per-instance")


if __name__ == "__main__":
    main()
