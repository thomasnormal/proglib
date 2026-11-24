#!/usr/bin/env python3
from pathlib import Path
import shutil, subprocess, tempfile
HERE = Path(__file__).resolve().parent
SOURCE = HERE / "localparam_logic.sv"
EXPECTED = ["ROW a=0 y=0001", "ROW a=15 y=1110"]
TB = '''module tb;
  logic [3:0] a; wire [3:0] y;
  localparam logic [3:0] OP = 4'd1;
  localparam_logic d(.a(a), .y(y));
  initial begin
    a=0; #1 $display("ROW a=%0d y=%b", a, y);
    a=15; #1 $display("ROW a=%0d y=%b", a, y);
    $finish;
  end
endmodule'''
def run(cmd, cwd):
    p = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=180)
    if p.returncode:
        raise RuntimeError(p.stdout)
    return p.stdout
def main():
    with tempfile.TemporaryDirectory(prefix="sv-localparam-logic-") as d:
        tb = Path(d) / "tb.sv"; tb.write_text(TB)
        exe = str(Path(d) / "sim")
        run(["iverilog", "-g2012", "-s", "tb", "-o", exe, str(SOURCE), str(tb)], d)
        rows = [x for x in run(["vvp", exe], d).splitlines() if x.startswith("ROW ")]
        if rows != EXPECTED:
            raise RuntimeError(f"Icarus: {rows} != {EXPECTED}")
        print("Icarus Verilog 13.0: 2 rows MATCH")
        if shutil.which("xrun"):
            rows = [x for x in run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "tb", str(SOURCE), str(tb)], d).splitlines() if x.startswith("ROW ")]
            if rows != EXPECTED:
                raise RuntimeError(f"Xcelium: {rows} != {EXPECTED}")
            print("Xcelium 24.03-s004: 2 rows MATCH")
if __name__ == "__main__":
    main()
