#!/usr/bin/env python3
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [
    "ROW reset rst=1 push=0 pop=0 din=00 dout=00 count=0",
    "ROW push0 rst=0 push=1 pop=0 din=a5 dout=a5 count=1",
    "ROW push1 rst=0 push=1 pop=0 din=3c dout=a5 count=2",
    "ROW pop0 rst=0 push=0 pop=1 din=3c dout=3c count=1",
    "ROW both rst=0 push=1 pop=1 din=5a dout=5a count=0",
    "ROW settled rst=0 push=0 pop=0 din=5a dout=5a count=0",
]


def run(args, cwd=ROOT):
    p = subprocess.run(args, cwd=cwd, text=True, stdout=subprocess.PIPE,
                       stderr=subprocess.STDOUT, timeout=120)
    if p.returncode:
        raise RuntimeError(p.stdout)
    return p.stdout


def rows(out):
    return [line for line in out.splitlines() if line.startswith("ROW ")]


def main():
    with tempfile.TemporaryDirectory(prefix="sv-e-fifo-edge-order-") as work:
        src = str(HERE / "fifo_edge_order_e.sv")
        tb = str(HERE / "fifo_edge_order_e_tb.sv")
        exe = str(Path(work) / "sim")
        run(["iverilog", "-g2012", "-s", "fifo_edge_order_e_tb", "-o", exe, src, tb], work)
        actual = rows(run(["vvp", exe], work))
    if actual != EXPECTED:
        raise RuntimeError(f"iverilog: {actual!r} != {EXPECTED!r}")
    print("Icarus Verilog 13.0: 6 rows MATCH")
    if shutil.which("xrun"):
        with tempfile.TemporaryDirectory(prefix="sv-e-fifo-edge-order-xrun-") as work:
            actual = rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                               "-top", "fifo_edge_order_e_tb", str(HERE / "fifo_edge_order_e.sv"),
                               str(HERE / "fifo_edge_order_e_tb.sv")], work))
        if actual != EXPECTED:
            raise RuntimeError(f"xrun: {actual!r} != {EXPECTED!r}")
        print("Xcelium 24.03-s004: 6 rows MATCH")
    else:
        print("no Xcelium result: xrun unavailable")
    run(["lake", "env", "lean",
         "Examples/system-verilog/sem2/fifo_edge_order_e/agree.lean"])
    print("ordinary E and hand-proof receipt: PASS")


if __name__ == "__main__":
    main()
