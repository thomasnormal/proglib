#!/usr/bin/env python3
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCE = HERE / "vector_multiplier_array_instance_e.sv"
ENVELOPE = HERE / (SOURCE.name + ".json")
EXPECTED = ["ROW 0100 xxxxxxxx", "ROW aaaa 00aa00aa", "ROW xxxx 00aa00aa"]
TB = """module tb;
  logic clk; logic [7:0] a [0:1]; wire [15:0] y [0:1];
  vector_multiplier_array_instance_e dut(.clk(clk),.a(a),.y(y));
  initial begin
    clk=0; a[0]=8'h01; a[1]=8'h00; #1 $display("ROW %h %h", {a[0],a[1]}, {y[0],y[1]});
    clk=1; a[0]=8'haa; a[1]=8'haa; #1 $display("ROW %h %h", {a[0],a[1]}, {y[0],y[1]});
    clk=0; a[0]=8'hxx; a[1]=8'hxx; #1 $display("ROW %h %h", {a[0],a[1]}, {y[0],y[1]});
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
             "vector_multiplier_array_instance_e", "-o", fresh.name,
             str(SOURCE.relative_to(ROOT))])
        if fresh.read() != ENVELOPE.read_bytes():
            raise RuntimeError("checked-in envelope differs from Slang extraction")
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    for simulator in ["iverilog"] + (["xrun"] if shutil.which("xrun") else []):
        with tempfile.TemporaryDirectory(prefix="sv-vector-child-array-") as directory:
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
