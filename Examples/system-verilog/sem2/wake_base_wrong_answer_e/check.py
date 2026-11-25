#!/usr/bin/env python3
"""Simulator receipt for the stale wake-base candidate."""
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCE = HERE / "wake_base_wrong_answer_e.sv"
ENVELOPE = HERE / (SOURCE.name + ".json")
EXPECTED = ["ROW seeded g=1 count=1", "ROW nba g=1 count=2"]
TB = r'''module tb;
  logic init, clk;
  logic g;
  integer count;
  wake_base_wrong_answer_e dut(.init(init), .clk(clk), .g(g), .count(count));
  initial begin
    init = 1'b0;
    clk = 1'b0;
    #1 init = 1'b1;
    #1 init = 1'b0;
    #1 $display("ROW seeded g=%b count=%0d", g, count);
    clk = 1'b1;
    #1 $display("ROW nba g=%b count=%0d", g, count);
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
    (ROOT / ".scratch").mkdir(exist_ok=True)
    with tempfile.NamedTemporaryFile(dir=ROOT / ".scratch", suffix=".json") as fresh:
        run(["python3", "extractors/sv/extract.py", "--top", HERE.name,
             "--retain-proc-rewrites", "-o", fresh.name,
             str(SOURCE.relative_to(ROOT))])
        if Path(fresh.name).read_bytes() != ENVELOPE.read_bytes():
            raise RuntimeError("checked-in envelope differs from Slang extraction")
    source = str(SOURCE)
    for simulator in ["iverilog"] + (["xrun"] if shutil.which("xrun") else []):
        with tempfile.TemporaryDirectory(dir=ROOT / ".scratch", prefix="sv-wake-base-") as work:
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
        print(f"{version}: 2 rows MATCH")


if __name__ == "__main__":
    main()
