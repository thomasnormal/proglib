#!/usr/bin/env python3
"""Differential receipt for time-zero continuous-assignment quiescence."""
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCES = [
    "time_zero_quiesce_nontopo.sv",
    "time_zero_quiesce_gclk.sv",
    "time_zero_quiesce_gclk2.sv",
]
TOPS = [p.removesuffix(".sv") for p in SOURCES]
TB = r'''module tb;
  logic d; logic a, b, q1, q2;
  time_zero_quiesce_nontopo n(.a(a), .b(b));
  time_zero_quiesce_gclk g1(.d(d), .q(q1));
  time_zero_quiesce_gclk2 g2(.d(d), .q(q2));
  initial begin
    d = 1'b1;
    #0 $display("ROW delta0 a=%b b=%b q1=%b q2=%b", a, b, q1, q2);
    #1 $display("ROW settled a=%b b=%b q1=%b q2=%b", a, b, q1, q2);
    $finish;
  end
endmodule'''


def run(cmd, cwd=ROOT):
    p = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=180)
    if p.returncode:
        raise RuntimeError(p.stdout)
    return p.stdout


def rows(output):
    return [line.split()[2:] for line in output.splitlines()
            if line.startswith("ROW ")]


def main():
    for source, top in zip(SOURCES, TOPS):
        run(["python3", "extractors/sv/extract.py", "--top", top,
             "--retain-proc-rewrites", "-o", str(HERE / (source + ".json")),
             str(HERE / source)])
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    expected_settled = ["a=1", "b=1", "q1=x", "q2=x"]
    with tempfile.TemporaryDirectory(prefix="sv-time-zero-quiesce-") as work:
        tb = Path(work) / "tb.sv"
        tb.write_text(TB)
        source_paths = [str(HERE / source) for source in SOURCES]
        for simulator in ("iverilog", "xrun"):
            if simulator == "iverilog":
                exe = str(Path(work) / "sim")
                run(["iverilog", "-g2012", "-s", "tb", "-o", exe,
                     *source_paths, str(tb)], work)
                output = run(["vvp", exe], work)
            else:
                output = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                              "-top", "tb", *source_paths, str(tb)], work)
            actual = rows(output)
            if actual[-1] != expected_settled:
                raise RuntimeError(f"{simulator}: settled {actual[-1]} != {expected_settled}")
            print(f"{simulator}: settled row MATCH a=1 b=1 q1=x q2=x; delta row {actual[0]}")
    print("E: quiesced initialState and both source orders agree")


if __name__ == "__main__":
    main()
