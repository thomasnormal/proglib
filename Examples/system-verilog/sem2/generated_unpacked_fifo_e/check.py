#!/usr/bin/env python3
from pathlib import Path
import shutil, subprocess, tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [
    "ROW 0 0 00000000 xxxxxxxx", "ROW 1 0 00000000 xxxxxxxx",
    "ROW 0 1 10100101 xxxxxxxx", "ROW 1 1 10100101 10100101",
    "ROW 0 0 xxxxxxxx 10100101", "ROW 1 0 xxxxxxxx 10100101",
    "ROW 0 1 zzzzzzzz 10100101", "ROW 1 1 zzzzzzzz zzzzzzzz",
]
def run(args, cwd=ROOT):
    p = subprocess.run(args, cwd=cwd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=180)
    if p.returncode:
        raise RuntimeError(p.stdout)
    return p.stdout
def rows(out):
    return [line for line in out.splitlines() if line.startswith("ROW ")]
def main():
    with tempfile.NamedTemporaryFile(suffix=".json") as f:
        run(["python3", "extractors/sv/extract.py", "--top", HERE.name,
             "--retain-proc-rewrites", "-o", f.name,
             str((HERE / (HERE.name + ".sv")).relative_to(ROOT))])
        if Path(f.name).read_bytes() != (HERE / (HERE.name + ".sv.json")).read_bytes():
            raise RuntimeError("envelope is stale")
    run(["lake", "build", "Examples.«system-verilog».sem2.generated_unpacked_fifo_e.agree"])
    print("extractor: generated unpacked FIFO envelope regenerates byte-identically")
    print("E: 8 rows MATCH: generated cells, x startup, z payload")
    src = str(HERE / (HERE.name + ".sv"))
    tb = '''module generated_unpacked_fifo_e_tb;
  logic clk, en; logic [7:0] d; wire [7:0] q;
  generated_unpacked_fifo_e #(.D(2), .W(8)) dut(.clk(clk), .en(en), .d(d), .q(q));
  task row(input logic c, input logic e, input logic [7:0] value);
    begin clk=c; en=e; d=value; #1 $display("ROW %b %b %b %b", c, e, value, q); end
  endtask
  initial begin
    row(0,0,8'h00); row(1,0,8'h00); row(0,1,8'ha5); row(1,1,8'ha5);
    row(0,0,8'bx); row(1,0,8'bx); row(0,1,8'bz); row(1,1,8'bz); $finish;
  end
endmodule
'''
    for simulator in ["iverilog"] + (["xrun"] if shutil.which("xrun") else []):
        with tempfile.TemporaryDirectory(prefix="sv-e-generated-unpacked-fifo-") as w:
            tb_path = Path(w) / "tb.sv"
            tb_path.write_text(tb)
            if simulator == "iverilog":
                exe = str(Path(w) / "sim")
                run(["iverilog", "-g2012", "-s", HERE.name + "_tb", "-o", exe, src, str(tb_path)], w)
                actual = rows(run(["vvp", exe], w))
                version = run(["iverilog", "-V"], w).splitlines()[0]
            else:
                actual = rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", HERE.name + "_tb", src, str(tb_path)], w))
                version = run(["xrun", "-version"], w).splitlines()[0]
        if actual != EXPECTED:
            raise RuntimeError(f"{simulator}: {actual!r} != {EXPECTED!r}")
        print(f"{version}: 8 rows MATCH E")
if __name__ == "__main__":
    main()
