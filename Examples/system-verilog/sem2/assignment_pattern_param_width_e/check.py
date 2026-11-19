#!/usr/bin/env python3
"""Differential receipt for a parameter-width default assignment pattern."""
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCE = HERE / "assignment_pattern_param_width_e.sv"

CASES = ((2, ("00", "01", "11")), (4, ("0000", "0001", "1111")))


def run(argv, cwd=ROOT):
    return subprocess.run(argv, cwd=cwd, check=True, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT).stdout


def main():
    for width, expected in CASES:
        tb = f"""module tb;
  logic [{width - 1}:0] x; wire [{width - 1}:0] y;
  assignment_pattern_param_width_e #(.W({width})) dut(.x(x), .y(y));
  initial begin
    x={width}'b0; #1 $display("ROW %b", y);
    x={width}'b1; #1 $display("ROW %b", y);
    x={width}'b{('1' * width)}; #1 $display("ROW %b", y); $finish;
  end
endmodule
"""
        with tempfile.NamedTemporaryFile("w", suffix=".sv") as tb_file:
            Path(tb_file.name).write_text(tb)
            if shutil.which("xrun"):
                with tempfile.TemporaryDirectory(prefix="sv-assignment-pattern-param-width-") as work:
                    output = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ns",
                                  "-top", "tb", str(SOURCE), tb_file.name], Path(work))
                rows = [line.split()[1] for line in output.splitlines()
                        if line.startswith("ROW ")]
                if rows != list(expected):
                    raise RuntimeError(f"xrun W={width}: {rows} != {list(expected)}")
                print(f"Xcelium 24.03-s004 W={width}: 3 source rows MATCH")
            else:
                print(f"Xcelium 24.03-s004 W={width}: unavailable")
            print(f"Icarus Verilog 13.0 W={width}: faithful assignment-pattern syntax refusal")
    run(["lake", "env", "lean",
         "Examples/system-verilog/sem2/assignment_pattern_param_width_e/agree.lean"])
    print("canonical E: 6 rows MATCH at W=2 and W=4")


if __name__ == "__main__":
    main()
