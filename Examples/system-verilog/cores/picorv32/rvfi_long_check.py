#!/usr/bin/env python3
"""Run the unchanged PicoRV32 source for 220 input-driven cycles.

The checker compares every printed output row from Icarus Verilog and Xcelium.
It does not compare a guessed model or alter the RTL.  A separate Lean probe
records canonical-E admission and execution status.
"""

from __future__ import annotations

import hashlib
from pathlib import Path
import re
import shutil
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[4]
SOURCE = ROOT / "Examples/system-verilog/cores/picorv32/picorv32_r2.v"
TB = ROOT / "Examples/system-verilog/cores/picorv32/rvfi_long_probe.v"
EXPECTED_CYCLES = 220
SOURCE_SHA256 = "0836050971b3c6cdd28ac3b1e5719a67fb645161912bef1e472e63995ceb0622"
ENVELOPE_SHA256 = "17ea7b66ab8ea9b6844c317928f0430cff8b8a5b53f658f7a929bf1aa6cdc236"


def run(command: list[str], cwd: Path) -> str:
    result = subprocess.run(command, cwd=cwd, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            check=False, timeout=180)
    if result.returncode:
        raise RuntimeError("command failed (%d): %s\n%s" %
                           (result.returncode, " ".join(command), result.stdout))
    return result.stdout


def rows(output: str) -> list[str]:
    result = [line.strip() for line in output.splitlines()
              if line.startswith("CYCLE ")]
    if len(result) != EXPECTED_CYCLES:
        raise RuntimeError("expected %d cycle rows, got %d" %
                           (EXPECTED_CYCLES, len(result)))
    return result


def check_program(trace: list[str]) -> None:
    retired = [line for line in trace if "rvfi_valid=1" in line]
    words = [re.search(r"rvfi_insn=([0-9a-f]{8})", line).group(1)
             for line in retired[:8]]
    expected = ["00500093", "00700113", "002081b3", "10302023",
                "10002203", "00418463", "02a00313", "00100073"]
    if words != expected:
        raise RuntimeError("unexpected retired program prefix: %s" % words)
    if "06300293" in words:
        raise RuntimeError("branch fall-through instruction retired")
    if "rvfi_mem_wmask=f" not in retired[3]:
        raise RuntimeError("store row has no full-word write mask")
    if "rvfi_mem_rmask=f" not in retired[4]:
        raise RuntimeError("load row has no full-word read mask")


def main() -> int:
    if shutil.which("iverilog") is None or shutil.which("vvp") is None:
        raise RuntimeError("Icarus Verilog 13.0 is required")
    if shutil.which("xrun") is None:
        raise RuntimeError("Xcelium 24.03-s004 is required")
    iverilog_version = run(["iverilog", "-V"], ROOT)
    if "Icarus Verilog version 13.0" not in iverilog_version:
        raise RuntimeError("unexpected Icarus version:\n%s" % iverilog_version)
    xrun_version = run(["xrun", "-version"], ROOT)
    if "24.03-s004" not in xrun_version:
        raise RuntimeError("unexpected Xcelium version:\n%s" % xrun_version)
    source_sha = hashlib.sha256(SOURCE.read_bytes()).hexdigest()
    envelope = ROOT / "Examples/system-verilog/cores/picorv32/picorv32_r2.sv.json"
    envelope_sha = hashlib.sha256(envelope.read_bytes()).hexdigest()
    if source_sha != SOURCE_SHA256:
        raise RuntimeError("RISCV_FORMAL source SHA-256 does not match the pinned receipt")
    if envelope_sha != ENVELOPE_SHA256:
        raise RuntimeError("RISCV_FORMAL envelope SHA-256 does not match the pinned receipt")
    with tempfile.TemporaryDirectory(prefix="picorv32-rvfi-long-") as work:
        directory = Path(work)
        ivvp = directory / "ivvp"
        run(["iverilog", "-g2012", "-DRISCV_FORMAL", "-s",
             "tb_picorv32_rvfi_long", "-o", str(ivvp), str(SOURCE), str(TB)],
            directory)
        icarus = rows(run(["vvp", str(ivvp)], directory))
        xcelium = rows(run(["xrun", "-sv", "-q", "-define", "RISCV_FORMAL",
                            "-top", "tb_picorv32_rvfi_long", str(SOURCE), str(TB)],
                           directory))
    if icarus != xcelium:
        for index, (left, right) in enumerate(zip(icarus, xcelium)):
            if left != right:
                raise RuntimeError("simulator mismatch at cycle %d\nIcarus: %s\nXcelium: %s" %
                                   (index, left, right))
        raise RuntimeError("simulator traces have different lengths")
    check_program(icarus)
    digest = hashlib.sha256("\n".join(icarus).encode()).hexdigest()
    print("Icarus Verilog 13.0 (s20250103-64-gdad78d525) and Xcelium 24.03-s004 agree on %d/%d cycles" %
          (len(icarus), EXPECTED_CYCLES))
    print("source SHA-256: %s" % source_sha)
    print("envelope SHA-256: %s" % envelope_sha)
    print("normalized cycle-row SHA-256: %s" % digest)
    print("program rows include ALU, BEQ, SW, and LW; mem_ready is held high")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
