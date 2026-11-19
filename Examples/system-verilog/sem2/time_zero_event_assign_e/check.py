#!/usr/bin/env python3
"""Differential receipt for continuous-assign time-zero event-source refusal."""
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCES = ["event_assign_gclk.sv", "event_assign_gclk2.sv"]
TB = r'''module tb;
  logic d, q1, q2;
  event_assign_gclk g1(.d(d), .q(q1));
  event_assign_gclk2 g2(.d(d), .q(q2));
  initial begin
    d = 1'b1;
    #0 $display("ROW delta0 q1=%b q2=%b", q1, q2);
    #1 $display("ROW settled q1=%b q2=%b", q1, q2);
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
    for source in SOURCES:
        top = source.removesuffix(".sv")
        run(["python3", "extractors/sv/extract.py", "--top", top,
             "--retain-proc-rewrites", "-o", str(HERE / (source + ".json")),
             str(HERE / source)])
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    with tempfile.TemporaryDirectory(prefix="sv-time-zero-event-") as work:
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
            print(f"{simulator}: delta {actual[0]} settled {actual[-1]} (race rows recorded)")
    print("E: both continuous-assign-driven event sources refused at time zero")

if __name__ == "__main__":
    main()
