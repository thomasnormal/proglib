#!/usr/bin/env python3
"""Differential receipt for the unknown array-bit-select audit witness."""
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCE = HERE / "arraybitsel_unknown_index_audit_e.sv"
ENVELOPE = HERE / (SOURCE.name + ".json")
EXPECTED = ["ROW 0 0 1", "ROW 1 1 1", "ROW x x 1", "ROW z z 1"]
TB = r'''module tb;
  logic d;
  wire q;
  arraybitsel_unknown_index_audit_e #(.WIDTH(2)) dut(.d(d), .q(q));
  initial begin
    d = 1'b0; #1 $display("ROW 0 %b %b", d, q);
    d = 1'b1; #1 $display("ROW 1 %b %b", d, q);
    d = 1'bx; #1 $display("ROW x %b %b", d, q);
    d = 1'bz; #1 $display("ROW z %b %b", d, q);
    $finish;
  end
endmodule
'''


def run(args, cwd=ROOT):
    result = subprocess.run(args, cwd=cwd, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            timeout=180)
    if result.returncode:
        raise RuntimeError(result.stdout)
    return result.stdout


def rows(output):
    return [line for line in output.splitlines() if line.startswith("ROW ")]


def main():
    with tempfile.NamedTemporaryFile(dir="/var/tmp", suffix=".json") as fresh:
        run(["python3", "extractors/sv/extract.py", "--top", HERE.name,
             "--retain-proc-rewrites", "-o", fresh.name,
             str(SOURCE.relative_to(ROOT))])
        if Path(fresh.name).read_bytes() != ENVELOPE.read_bytes():
            raise RuntimeError("checked-in envelope differs from Slang extraction")
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    print("ordinary E: source-shaped process count 3 and q=1 after unknown index")

    source = str(SOURCE)
    simulator_rows = {}
    for simulator in ["iverilog"] + (["xrun"] if shutil.which("xrun") else []):
        with tempfile.TemporaryDirectory(dir="/var/tmp", prefix="sv-arraybitsel-audit-") as work:
            work_path = Path(work)
            tb = work_path / "tb.sv"
            tb.write_text(TB)
            if simulator == "iverilog":
                executable = work_path / "sim"
                run(["iverilog", "-g2012", "-s", "tb", "-o", str(executable),
                     source, str(tb)], work)
                output = run(["vvp", str(executable)], work)
                version = run(["iverilog", "-V"], work).splitlines()[0]
            else:
                output = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                              "-top", "tb", source, str(tb)], work)
                version = run(["xrun", "-version"], work).splitlines()[0]
        actual = rows(output)
        if actual != EXPECTED:
            raise RuntimeError(f"{simulator}: {actual!r} != {EXPECTED!r}")
        simulator_rows[simulator] = actual
        print(f"{version}: 4 rows MATCH E")
    if len(simulator_rows) == 2 and len(set(map(tuple, simulator_rows.values()))) != 1:
        raise RuntimeError("pinned simulator rows diverge")


if __name__ == "__main__":
    main()
