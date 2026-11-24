#!/usr/bin/env python3
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCE = HERE / "generated_instance_timeout_e.sv"
ENVELOPE = HERE / (SOURCE.name + ".json")
EXPECTED = [["0"], ["0"], ["0"], ["1"]]

TB = """module tb;
  logic clk, rstn, d;
  wire q;
  generated_instance_timeout_e dut(.d(d), .q(q), .clk(clk), .rstn(rstn));
  initial begin
    clk = 0; rstn = 0; d = 0; #1 $display("ROW %b", q);
    clk = 1; rstn = 1; d = 1; #1 $display("ROW %b", q);
    clk = 0; d = 0; #1 $display("ROW %b", q);
    clk = 1; #1 $display("ROW %b", q);
    $finish;
  end
endmodule
"""


def run(command, cwd=ROOT):
    result = subprocess.run(command, cwd=cwd, text=True,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=180)
    if result.returncode:
        raise RuntimeError(result.stdout)
    return result.stdout


def rows(output):
    return [[line.split()[1]] for line in output.splitlines()
            if line.startswith("ROW ")]


def main():
    with tempfile.NamedTemporaryFile(suffix=".json") as fresh:
        run(["python3", "extractors/sv/extract.py", "--top",
             "generated_instance_timeout_e", "-o", fresh.name,
             str(SOURCE.relative_to(ROOT))])
        if fresh.read() != ENVELOPE.read_bytes():
            raise RuntimeError("checked-in envelope differs from Slang extraction")

    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    for simulator in ["iverilog"] + (["xrun"] if shutil.which("xrun") else []):
        with tempfile.TemporaryDirectory(prefix="sv-generated-child-") as directory:
            directory = Path(directory)
            tb = directory / "tb.sv"
            tb.write_text(TB)
            if simulator == "iverilog":
                executable = directory / "sim"
                run(["iverilog", "-g2012", "-s", "tb", "-o", str(executable),
                     str(SOURCE), str(tb)], directory)
                output = run(["vvp", str(executable)], directory)
                version = run(["iverilog", "-V"], directory).splitlines()[0]
            else:
                output = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                              "-top", "tb", str(SOURCE), str(tb)], directory)
                version = run(["xrun", "-version"], directory).splitlines()[0]
        actual = rows(output)
        if actual != EXPECTED:
            raise RuntimeError(f"{simulator}: {actual} != {EXPECTED}")
        print(f"{version}: {len(actual)} rows MATCH")


if __name__ == "__main__":
    main()
