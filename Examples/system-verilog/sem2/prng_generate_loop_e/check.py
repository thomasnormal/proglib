#!/usr/bin/env python3
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCE = HERE / "prng_generate_loop_e.sv"
ENVELOPE = HERE / (SOURCE.name + ".json")
EXPECTED = ["ROW 000 000", "ROW 111 111", "ROW xxx 111"]
TB = """module tb;
  logic clk,rstn; logic [2:0] d; wire [2:0] q;
  prng_generate_loop_e dut(.clk(clk),.rstn(rstn),.d(d),.q(q));
  initial begin
    clk=0; rstn=0; d=3'b000; #1 $display("ROW %b %b",d,q);
    clk=1; rstn=1; d=3'b111; #1 $display("ROW %b %b",d,q);
    clk=0; d=3'bxxx; #1 $display("ROW %b %b",d,q);
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
        run(["python3", "extractors/sv/extract.py", "--top", "prng_generate_loop_e",
             "-o", fresh.name, str(SOURCE.relative_to(ROOT))])
        if fresh.read() != ENVELOPE.read_bytes():
            raise RuntimeError("checked-in envelope differs from Slang extraction")
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    simulator_rows = {}
    for simulator in ["iverilog"] + (["xrun"] if shutil.which("xrun") else []):
        with tempfile.TemporaryDirectory(prefix="sv-prng-generate-") as directory:
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
        simulator_rows[simulator] = rows
        print(f"{version}: {len(rows)} rows captured")
    if len(simulator_rows) == 2:
        values = list(simulator_rows.values())
        print("pinned simulators: rows MATCH" if values[0] == values[1]
              else "pinned simulators: rows DIVERGE")
    print("clocked sv_structure: named for-generate refusal remains")

if __name__ == "__main__":
    main()
