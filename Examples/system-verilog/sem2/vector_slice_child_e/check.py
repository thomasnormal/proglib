#!/usr/bin/env python3
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCE = HERE / "vector_slice_child_e.sv"
ENVELOPE = HERE / (SOURCE.name + ".json")
EXPECTED = ["ROW 0102 00010002", "ROW a5a5 00a500a5", "ROW xxxx 00xx00xx"]
TB = """module tb;
  logic [1:0][7:0] a; wire [1:0][15:0] y;
  vector_slice_child_e dut(.a(a),.y(y));
  initial begin
    a=16'h0102; #1 $display("ROW %h %h", a, y);
    a=16'ha5a5; #1 $display("ROW %h %h", a, y);
    a=16'hxxxx; #1 $display("ROW %h %h", a, y);
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
        run(["python3", "extractors/sv/extract.py", "--top", "vector_slice_child_e",
             "-o", fresh.name, str(SOURCE.relative_to(ROOT))])
        if fresh.read() != ENVELOPE.read_bytes():
            raise RuntimeError("checked-in envelope differs from Slang extraction")
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    for simulator in ["iverilog"] + (["xrun"] if shutil.which("xrun") else []):
        with tempfile.TemporaryDirectory(prefix="sv-vector-slice-child-") as directory:
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
