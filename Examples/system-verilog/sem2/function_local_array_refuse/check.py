#!/usr/bin/env python3
"""Receipt for the automatic function-local unpacked-array boundary."""
from pathlib import Path
import os
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCE = HERE / "function_local_array_refuse.sv"


def main() -> None:
    subprocess.run(["lake", "env", "lean", str(HERE / "agree.lean")],
                   cwd=ROOT, check=True, timeout=180)
    census = subprocess.run(
        ["python3", "harness/sv/refusal_census.py", "ordinary",
         str(HERE / "function_local_array_refuse.sv.json")],
        cwd=ROOT, check=True, text=True, stdout=subprocess.PIPE,
    ).stdout
    if "E memory route does not yet admit module member 'SubroutineSymbol:Subroutine'" not in census:
        raise RuntimeError(f"missing function-local-array refusal: {census}")
    print("canonical E: EXPECTED function-local unpacked-array refusal")
    tb_text = '''module tb; logic [7:0] x; wire [7:0] y;
function_local_array dut(.x(x), .y(y));
initial begin
  x=8'h00; #1 $display("ROW 0 y=%b", y);
  x=8'h03; #1 $display("ROW 1 y=%b", y);
  x=8'h08; #1 $display("ROW 2 y=%b", y);
  x=8'hxx; #1 $display("ROW 3 y=%b", y);
  x=8'hzz; #1 $display("ROW 4 y=%b", y);
  $finish;
end
endmodule
'''
    expected = [
        "ROW 0 y=10100101",
        "ROW 1 y=00010100",
        "ROW 2 y=10101101",
        "ROW 3 y=xxxxxxxx",
        "ROW 4 y=xxxxxxxx",
    ]
    scratch = os.environ.get("TMPDIR")
    if not scratch:
        raise RuntimeError("TMPDIR must point to lane scratch")
    for sim in ("iverilog", "xrun"):
        with tempfile.TemporaryDirectory(prefix=f"sv-function-local-{sim}-",
                                          dir=scratch) as work_name:
            work = Path(work_name)
            tb = work / "tb.sv"
            tb.write_text(tb_text)
            if sim == "iverilog":
                exe = work / "sim"
                subprocess.run(["iverilog", "-g2012", "-s", "tb", "-o",
                                str(exe), str(SOURCE), str(tb)],
                               cwd=work, check=True, timeout=180)
                output = subprocess.run(["vvp", str(exe)], cwd=work,
                                        check=True, text=True,
                                        stdout=subprocess.PIPE,
                                        timeout=180).stdout
            else:
                output = subprocess.run(
                    ["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                     "-top", "tb", str(SOURCE), str(tb)],
                    cwd=work, check=True, text=True,
                    stdout=subprocess.PIPE, timeout=180).stdout
            rows = [line for line in output.splitlines()
                    if line.startswith("ROW ")]
            if rows != expected:
                raise RuntimeError(f"{sim}: {rows} != {expected}\n{output}")
        print(f"{sim}: {len(expected)} source rows MATCH")


if __name__ == "__main__":
    main()
