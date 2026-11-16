#!/usr/bin/env python3
"""Receipt for canonical-E quiescence of a non-topological assign chain."""
from pathlib import Path
import json
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
ENV = HERE / "non_topological_assign.sv.json"
EXPECTED = [["0", "0"], ["1", "1"], ["x", "x"], ["z", "z"]]
TB = r'''module tb; logic x; wire y;
non_topological_assign dut(.x(x),.y(y));
initial begin x=0;#1 $display("ROW %b %b",x,y); x=1;#1 $display("ROW %b %b",x,y);
x=1'bx;#1 $display("ROW %b %b",x,y); x=1'bz;#1 $display("ROW %b %b",x,y); $finish; end
endmodule'''


def main():
    source = "Examples/system-verilog/sem2/non_topological_assign/non_topological_assign.sv"
    envelope = "Examples/system-verilog/sem2/non_topological_assign/non_topological_assign.sv.json"
    subprocess.run(["python3", "extractors/sv/extract.py", "--top", "non_topological_assign",
                    "-o", envelope, source], cwd=ROOT, check=True)
    text = subprocess.run(["python3", "harness/sv/refusal_census.py", "ordinary", envelope],
                          cwd=ROOT, check=True, text=True, stdout=subprocess.PIPE).stdout
    rows = [json.loads(x) for x in text.splitlines()]
    refusal = [r for r in rows if r.get("construct") == "Instantiation:E:unsupported"]
    if refusal:
        raise RuntimeError(f"canonical E still refuses the non-topological chain: {rows}")
    with tempfile.TemporaryDirectory(prefix="sv-topology-") as work:
        tb = Path(work) / "tb.sv"; tb.write_text(TB)
        outputs = []
        for sim in ("iverilog", "xrun"):
            if sim == "iverilog":
                exe = str(Path(work) / "sim")
                subprocess.run(["iverilog", "-g2012", "-s", "tb", "-o", exe,
                                str(HERE / "non_topological_assign.sv"), str(tb)], cwd=work, check=True)
                out = subprocess.run(["vvp", exe], cwd=work, check=True, text=True,
                                     stdout=subprocess.PIPE).stdout
            else:
                out = subprocess.run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "tb",
                                      str(HERE / "non_topological_assign.sv"), str(tb)], cwd=work,
                                     check=True, text=True, stdout=subprocess.PIPE).stdout
            actual = [line.split()[1:] for line in out.splitlines() if line.startswith("ROW ")]
            if actual != EXPECTED:
                raise RuntimeError(f"{sim}: {actual} != {EXPECTED}")
            print(f"{sim}: 4 x/z rows MATCH")
    lean = subprocess.run(["lake", "env", "lean", str(HERE / "agree.lean")],
                          cwd=ROOT, check=True, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(lean.stdout, end="")
    print("ordinary census: no Instantiation:E:unsupported topology refusal")


if __name__ == "__main__":
    main()
