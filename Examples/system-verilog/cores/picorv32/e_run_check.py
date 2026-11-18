#!/usr/bin/env python3
"""Reproduce the PicoRV32 input-driven simulator and canonical-E receipt.

The pinned simulators must agree on every sampled row. Canonical E is then
loaded at the same 26-parameter point. Its first running boundary is the
reactive dependency-order refusal, so the receipt records zero E cycles and
the exact refusal instead of treating a simulator trace as an E result.
"""

from __future__ import annotations

import hashlib
from pathlib import Path
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[4]
CHECKER = ROOT / "Examples/system-verilog/cores/picorv32/rvfi_long_check.py"
SOURCE = ROOT / "Examples/system-verilog/cores/picorv32/picorv32_r2.v"
ENVELOPE = ROOT / "Examples/system-verilog/cores/picorv32/picorv32_r2.sv.json"
SOURCE_SHA256 = "0836050971b3c6cdd28ac3b1e5719a67fb645161912bef1e472e63995ceb0622"
ENVELOPE_SHA256 = "17ea7b66ab8ea9b6844c317928f0430cff8b8a5b53f658f7a929bf1aa6cdc236"
EXPECTED = (
    "Comb:dependency-order: 9.2.2.2/9.4.2.2: reactive process reads "
    "'alu_eq' from itself or a later reactive process; canonical E has no "
    "fixed-point scheduler"
)
ARGS = (
    "1 1 1 1 0 1 0 0 0 0 1 1 0 0 0 0 0 1 1 0 0 0 4294967295 0 16 "
    "4294967295"
)


def run(command: list[str], cwd: Path, timeout: int = 180) -> str:
    result = subprocess.run(
        command,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
        timeout=timeout,
    )
    if result.returncode:
        raise RuntimeError(
            "command failed (%d): %s\n%s"
            % (result.returncode, " ".join(command), result.stdout)
        )
    return result.stdout


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def canonical_e_receipt() -> str:
    envelope = str(ENVELOPE).replace("\\", "\\\\").replace('"', '\\"')
    lean_source = f'''import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
open LeanModels.Sv LeanModels.Sv.Kernel
set_option maxRecDepth 100000 in
load_design_sv2 picorv32_step_wall from "{envelope}"
#eval match picorv32_step_wall.e {ARGS} with
| .unsupported msg => "E-RUN: 0/220 cycles; wall: " ++ msg
| .ok _ => "unexpected canonical-E admission"
| .timeout => "unexpected canonical-E timeout"
'''
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", prefix="picorv32-e-run-", delete=False
    ) as handle:
        handle.write(lean_source)
        script = Path(handle.name)
    try:
        return run(["lake", "env", "lean", str(script)], ROOT)
    finally:
        script.unlink(missing_ok=True)


def main() -> int:
    if sha256(SOURCE) != SOURCE_SHA256:
        raise RuntimeError("PicoRV32 source SHA-256 does not match the pinned receipt")
    if sha256(ENVELOPE) != ENVELOPE_SHA256:
        raise RuntimeError("PicoRV32 envelope SHA-256 does not match the pinned receipt")
    simulator = run(["python3", str(CHECKER)], ROOT)
    if "agree on 220/220 cycles" not in simulator:
        raise RuntimeError("simulator receipt did not report 220/220 agreement")
    e_run = canonical_e_receipt()
    expected = "E-RUN: 0/220 cycles; wall: " + EXPECTED
    if expected not in e_run:
        raise RuntimeError("canonical-E receipt did not reproduce the pinned wall\n" + e_run)
    print("source SHA-256: " + SOURCE_SHA256)
    print("envelope SHA-256: " + ENVELOPE_SHA256)
    print(simulator, end="")
    print(expected)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
