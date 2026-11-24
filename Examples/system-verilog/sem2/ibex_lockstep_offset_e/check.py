#!/usr/bin/env python3
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCE = HERE / "ibex_lockstep_offset_e.sv"
ENVELOPE = HERE / (SOURCE.name + ".json")
EXPECTED = ["ROW 000 000", "ROW 101 101", "ROW xxx xxx", "ROW zzz zzz"]
TB = """module tb;
  logic [2:0] i; wire [2:0] o;
  ibex_lockstep_offset_e dut(.i(i), .o(o));
  initial begin
    i=3'b000; #1 $display("ROW %b %b", i, o);
    i=3'b101; #1 $display("ROW %b %b", i, o);
    i=3'bxxx; #1 $display("ROW %b %b", i, o);
    i=3'bzzz; #1 $display("ROW %b %b", i, o);
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
             "ibex_lockstep_offset_e", "-o", fresh.name,
             str(SOURCE.relative_to(ROOT))])
        if fresh.read() != ENVELOPE.read_bytes():
            raise RuntimeError("checked-in envelope differs from Slang extraction")
    census = run(["python3", "harness/sv/refusal_census.py", "ordinary", str(ENVELOPE)])
    if "function 'vbits' in a constant context" not in census:
        raise RuntimeError(f"ordinary route did not retain the named wall: {census}")
    print("ordinary route: loud constant-function refusal at LockstepOffsetW")
    for simulator in ["iverilog"] + (["xrun"] if shutil.which("xrun") else []):
        with tempfile.TemporaryDirectory(prefix="sv-ibex-lockstep-") as directory:
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
