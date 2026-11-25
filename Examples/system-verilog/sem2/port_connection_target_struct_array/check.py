#!/usr/bin/env python3
"""Receipt for the faithful structured port-connection target wall."""
from pathlib import Path
import json
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
ENV = HERE / "port_connection_target_struct_array.sv.json"
EXPECTED = [["0", "0000"], ["1", "1111"], ["x", "xxxx"], ["z", "zzzz"]]
TB = r'''module tb; logic d; wire [3:0] y;
register_parent dut(.d(d),.y(y));
initial begin d=0;#1 $display("ROW %b %b",d,y); d=1;#1 $display("ROW %b %b",d,y);
d=1'bx;#1 $display("ROW %b %b",d,y); d=1'bz;#1 $display("ROW %b %b",d,y); $finish; end
endmodule'''


def main():
    source = "Examples/system-verilog/sem2/port_connection_target_struct_array/port_connection_target_struct_array.sv"
    envelope = "Examples/system-verilog/sem2/port_connection_target_struct_array/port_connection_target_struct_array.sv.json"
    subprocess.run(["python3", "extractors/sv/extract.py", "--top", "register_parent",
                    "-o", envelope, source],
                   cwd=ROOT, check=True)
    census = subprocess.run(["python3", "harness/sv/refusal_census.py", "ordinary", str(ENV)],
                            cwd=ROOT, check=True, text=True, stdout=subprocess.PIPE).stdout
    rows = [json.loads(x) for x in census.splitlines()]
    refusal = [r for r in rows if r.get("construct") == "Instantiation:E:unsupported"]
    if len(refusal) != 1 or refusal[0]["function"] != "PDesign.instantiateE2":
        raise RuntimeError(f"unexpected ordinary census: {rows}")
    if not refusal[0]["message"].startswith("Schedule:preemptive:"):
        raise RuntimeError(f"unexpected refusal: {refusal[0]}")
    with tempfile.TemporaryDirectory(prefix="sv-port-target-") as work:
        tb = Path(work) / "tb.sv"; tb.write_text(TB)
        p = subprocess.run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "tb",
                            str(HERE / "port_connection_target_struct_array.sv"), str(tb)],
                           cwd=work, text=True, stdout=subprocess.PIPE,
                           stderr=subprocess.STDOUT, check=True)
    actual = [line.split()[1:] for line in p.stdout.splitlines() if line.startswith("ROW ")]
    if actual != EXPECTED:
        raise RuntimeError(f"Xcelium: {actual} != {EXPECTED}")
    print("ordinary census: Schedule:preemptive / PDesign.instantiateE2")
    print("Xcelium 24.03-s004: 4 x/z rows MATCH")
    print("Icarus: unsupported unpacked structs; no oracle result claimed")


if __name__ == "__main__":
    main()
