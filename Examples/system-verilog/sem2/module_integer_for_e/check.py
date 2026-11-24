#!/usr/bin/env python3
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCE = HERE / "module_integer_for_e.sv"
ENVELOPE = HERE / (SOURCE.name + ".json")
EXPECTED = ["ROW 00 xx", "ROW 11 11", "ROW xx 11", "ROW zz zz"]
TB = """module tb;
  logic clk,en; logic [1:0] d; wire [1:0] q;
  module_integer_for_e dut(.clk(clk),.en(en),.d(d),.q(q));
  initial begin
    clk=0; en=0; d=2'b00; #1 $display("ROW %b %b",d,q);
    clk=1; en=1; d=2'b11; #1 $display("ROW %b %b",d,q);
    clk=0; en=0; d=2'bxx; #1 $display("ROW %b %b",d,q);
    clk=1; en=1; d=2'bzz; #1 $display("ROW %b %b",d,q);
    $finish;
  end
endmodule
"""

def run(command, cwd=ROOT):
    result = subprocess.run(command, cwd=cwd, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            timeout=180)
    if result.returncode:
        raise RuntimeError(result.stdout)
    return result.stdout

def main():
    with tempfile.NamedTemporaryFile(suffix=".json") as fresh:
        run(["python3", "extractors/sv/extract.py", "--top",
             "module_integer_for_e", "-o", fresh.name,
             str(SOURCE.relative_to(ROOT))])
        if fresh.read() != ENVELOPE.read_bytes():
            raise RuntimeError("checked-in envelope differs from Slang extraction")
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    for simulator in ["iverilog"] + (["xrun"] if shutil.which("xrun") else []):
        with tempfile.TemporaryDirectory(prefix="sv-module-integer-") as directory:
            directory = Path(directory); tb = directory / "tb.sv"; tb.write_text(TB)
            if simulator == "iverilog":
                executable = directory / "sim"
                run(["iverilog", "-g2012", "-s", "tb", "-o", str(executable), str(SOURCE), str(tb)], directory)
                output = run(["vvp", str(executable)], directory)
                version = run(["iverilog", "-V"], directory).splitlines()[0]
            else:
                output = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "tb", str(SOURCE), str(tb)], directory)
                version = run(["xrun", "-version"], directory).splitlines()[0]
        rows = [line for line in output.splitlines() if line.startswith("ROW ")]
        if rows != EXPECTED:
            raise RuntimeError(f"{simulator}: {rows} != {EXPECTED}")
        print(f"{version}: {len(rows)} rows MATCH")

if __name__ == "__main__":
    main()
