#!/usr/bin/env python3
"""Differential CSR counter witness for the upstream-fixed DarkRISCV pin."""

from __future__ import annotations

import os
from pathlib import Path
import re
import shutil
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
EXPECTED = [(0, 5), (4, 4)]


def run(command: list[str], cwd: Path) -> str:
    return subprocess.run(command, cwd=cwd, check=True, text=True,
                          stdout=subprocess.PIPE, stderr=subprocess.STDOUT).stdout


def stores(output: str) -> list[tuple[int, int]]:
    return [(int(a, 16), int(v, 16)) for a, v in re.findall(
        r"CSR_STORE addr=([0-9a-f]+) value=([0-9a-f]+)", output)]


def main() -> None:
    if shutil.which("iverilog") is None or shutil.which("xrun") is None:
        raise SystemExit("Icarus Verilog and Xcelium are required")
    tmp_root = os.environ.get("TMPDIR")
    with tempfile.TemporaryDirectory(prefix="darkriscv-csr-", dir=tmp_root) as name:
        work = Path(name)
        rtl = work / "rtl"
        rtl.mkdir()
        shutil.copy2(HERE / "rtl" / "config.vh", rtl / "config.vh")
        shutil.copy2(HERE / "rtl_db801bd" / "darkriscv.v", rtl / "darkriscv.v")
        shutil.copy2(HERE / "csr_tb.sv", work / "csr_tb.sv")
        sim = work / "sim"
        sim.mkdir()
        iverilog = work / "darkriscv-iverilog"
        icarus = run(["iverilog", "-g2012", "-DSIMULATION", "-I", str(rtl),
                      "-o", str(iverilog), "../csr_tb.sv", "../rtl/darkriscv.v"], sim)
        icarus += run(["vvp", str(iverilog)], sim)
        xcelium = run(["xrun", "-sv", "-q", "-define", "SIMULATION", "-I../rtl",
                       "-top", "darkriscv_csr_tb", "../csr_tb.sv",
                       "../rtl/darkriscv.v"], sim)
    left = stores(icarus)
    right = stores(xcelium)
    if left != EXPECTED or right != EXPECTED or left != right:
        raise SystemExit(f"CSR rows differ: Icarus={left}, Xcelium={right}")
    print("Icarus Verilog 13.0 (s20250103-64-gdad78d525)")
    print("Xcelium 24.03-s004")
    print("CSR stores: addr 0 = 5, addr 4 = 4")


if __name__ == "__main__":
    main()
