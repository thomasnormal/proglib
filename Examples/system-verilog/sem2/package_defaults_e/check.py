#!/usr/bin/env python3
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCE = HERE / "package_defaults_e.sv"
EXPECTED = [
    "ROW 1 10 01 aa 1 10 01 aa",
    "ROW a 01 10 55 a 01 10 55",
    "ROW x xx xx xx x xx xx xx",
]

TB = """module tb;
  logic [3:0] i_default;
  wire [3:0] o_default;
  logic [1:0] i_chain;
  wire [1:0] o_chain;
  logic [1:0] i_local;
  wire [1:0] o_local;
  logic [7:0] i_typed;
  wire [7:0] o_typed;
  package_defaults_e dut(
    .i_default(i_default), .o_default(o_default),
    .i_chain(i_chain), .o_chain(o_chain),
    .i_local(i_local), .o_local(o_local),
    .i_typed(i_typed), .o_typed(o_typed));
  initial begin
    i_default = 4'h1; i_chain = 2'b10; i_local = 2'b01; i_typed = 8'haa;
    #1 $display("ROW %h %b %b %h %h %b %b %h", i_default, i_chain, i_local, i_typed,
      o_default, o_chain, o_local, o_typed);
    i_default = 4'ha; i_chain = 2'b01; i_local = 2'b10; i_typed = 8'h55;
    #1 $display("ROW %h %b %b %h %h %b %b %h", i_default, i_chain, i_local, i_typed,
      o_default, o_chain, o_local, o_typed);
    i_default = 4'hx; i_chain = 2'bxx; i_local = 2'bxx; i_typed = 8'hxx;
    #1 $display("ROW %h %b %b %h %h %b %b %h", i_default, i_chain, i_local, i_typed,
      o_default, o_chain, o_local, o_typed);
    $finish;
  end
endmodule
"""


def run(cmd, cwd=ROOT):
    result = subprocess.run(
        cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, timeout=180,
    )
    if result.returncode:
        raise RuntimeError(result.stdout)
    return result.stdout


def main():
    with tempfile.NamedTemporaryFile(suffix=".json") as envelope:
        run([
            "python3", "extractors/sv/extract.py", "--top", "package_defaults_e",
            "-o", envelope.name, str(SOURCE.relative_to(ROOT)),
        ])
        if envelope.read() != (HERE / (SOURCE.name + ".json")).read_bytes():
            raise RuntimeError("stale envelope")

    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    for simulator in ["iverilog"] + (["xrun"] if shutil.which("xrun") else []):
        with tempfile.TemporaryDirectory(prefix="sv-pkg-defaults-") as directory:
            directory = Path(directory)
            testbench = directory / "tb.sv"
            testbench.write_text(TB)
            if simulator == "iverilog":
                executable = directory / "sim"
                run(["iverilog", "-g2012", "-s", "tb", "-o", str(executable), str(SOURCE), str(testbench)], directory)
                output = run(["vvp", str(executable)], directory)
                version = run(["iverilog", "-V"], directory).splitlines()[0]
            else:
                output = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "tb", str(SOURCE), str(testbench)], directory)
                version = run(["xrun", "-version"], directory).splitlines()[0]
        rows = [line for line in output.splitlines() if line.startswith("ROW ")]
        if rows != EXPECTED:
            raise RuntimeError(f"{simulator}: {rows} != {EXPECTED}")
        print(f"{version}: {len(rows)} rows MATCH")


if __name__ == "__main__":
    main()
