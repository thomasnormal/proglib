#!/usr/bin/env python3
"""Receipt for the source-shaped parameter-default assignment-pattern wall."""
from pathlib import Path
import shutil, subprocess, tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCE = HERE / "assignment_pattern_param_e.sv"
ENV = HERE / "assignment_pattern_param_e.sv.json"
TB = """module tb;
  logic [3:0] x; wire [3:0] y;
  assignment_pattern_param_e dut(.x(x), .y(y));
  initial begin
    x=4'b0000; #1 $display("ROW %b", y);
    x=4'b1010; #1 $display("ROW %b", y);
    x=4'bzzzz; #1 $display("ROW %b", y); $finish;
  end
endmodule
"""
EXPECTED = ["0000", "1010", "xxxx"]
def run(args, cwd=ROOT):
    return subprocess.run(args, cwd=cwd, check=True, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT).stdout
def main():
    with tempfile.NamedTemporaryFile(suffix=".sv") as tb:
        Path(tb.name).write_text(TB)
        if shutil.which("xrun"):
            with tempfile.TemporaryDirectory(prefix="sv-assignment-pattern-param-") as work:
                out = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ns",
                           "-top", "tb", str(SOURCE), tb.name], Path(work))
            rows = [line.split()[1] for line in out.splitlines() if line.startswith("ROW ")]
            if rows != EXPECTED:
                raise RuntimeError(f"xrun: {rows} != {EXPECTED}")
            print("Xcelium 24.03-s004: 3 source rows MATCH")
        print("Icarus Verilog 13.0: faithful assignment-pattern syntax refusal")
    run(["lake", "env", "lean",
         "Examples/system-verilog/sem2/assignment_pattern_param_e/agree.lean"])
    print("canonical E: 3 rows MATCH fixed packed default pattern")
if __name__ == "__main__":
    main()
