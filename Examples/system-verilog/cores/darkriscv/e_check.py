#!/usr/bin/env python3
"""Check the pinned DarkRISCV envelope through canonical E."""

from __future__ import annotations

import hashlib
import os
from pathlib import Path
import subprocess
import tempfile


ENVELOPE_REFUSAL = {
    "38b3c3253f79b006aac7a547d9c61fce31c86dfe26994a990ce324bd1ce321cf":
        "decl 'FLUSH': non-literal initializer outside the M0 tier",
    "5038a315ae61f44951ed400f61632ee29dfa30d7c1b092d5f5cddbafcd55243b":
        "decl 'FLUSH': non-literal initializer outside the M0 tier",
    "ca8f0a92c7477ee9fd75f55966c122fa29400f8948a18ae361cc81a077077fc5":
        "decl 'REGS': unpacked array storage outside E (UnpackedDecl:memory)",
}

COREMEM_ENVELOPE = "ca8f0a92c7477ee9fd75f55966c122fa29400f8948a18ae361cc81a077077fc5"


def main() -> None:
    envelope_text = os.environ.get("DARKRISCV_ENVELOPE")
    if not envelope_text:
        raise SystemExit("set DARKRISCV_ENVELOPE to the pinned envelope")
    envelope = Path(envelope_text).resolve()
    if not envelope.is_file():
        raise SystemExit(f"missing pinned envelope: {envelope.name}")
    digest = hashlib.sha256(envelope.read_bytes()).hexdigest()
    expected_refusal = ENVELOPE_REFUSAL.get(digest)
    if expected_refusal is None:
        raise SystemExit(f"envelope SHA-256 {digest} is not a pinned receipt")

    path = str(envelope).replace("\\", "\\\\").replace('"', '\\"')
    lean_source = f'''import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
open LeanModels.Sv LeanModels.Sv.Kernel
set_option maxRecDepth 100000 in
load_design_sv2 dark from "{path}"
def bits (w n : Nat) := LVec.ofNat w n
def row (res : Nat) : SvState := [("CLK", bits 1 0), ("RES", bits 1 res), ("IRQ", bits 32 0),
  ("IDATA", bits 32 19), ("IDACK", bits 1 1), ("IBERR", bits 1 0),
  ("DATAI", bits 32 0), ("DDACK", bits 1 1), ("DBERR", bits 1 0)]
#eval match PDesign.instantiateCoreMem dark.pdesign [0] with
| .ok d => match d.initialState with
  | .ok st => match d.stepOnePassTrace st (row 1) with
    | .ok (st1, _) => match d.stepOnePassTrace st1 (row 0) with
      | .ok _ => "initial-ok\ntwo-pass-ok"
      | .timeout => "initial-ok\nsecond-pass-timeout"
      | .unsupported m => "initial-ok\nsecond-pass-unsupported: " ++ m
    | .timeout => "initial-ok\none-pass-timeout"
    | .unsupported m => "initial-ok\none-pass-unsupported: " ++ m
  | .timeout => "initial-timeout"
  | .unsupported m => "initial-unsupported: " ++ m
| .timeout => "instantiate-timeout"
| .unsupported m => "instantiate-unsupported: " ++ m
'''
    repo = Path(__file__).resolve().parents[4]
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", prefix="darkriscv-e-", delete=False
    ) as handle:
        handle.write(lean_source)
        script = Path(handle.name)
    try:
        result = subprocess.run(
            ["lake", "env", "lean", str(script)],
            cwd=repo,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
    finally:
        script.unlink(missing_ok=True)
    if result.returncode != 0:
        raise SystemExit(result.stdout)
    if digest == COREMEM_ENVELOPE:
        if '"initial-ok\\ntwo-pass-ok"' not in result.stdout:
            raise SystemExit("canonical-E memory cycle probe did not complete two passes")
        print("canonical E: loaded one-rank memory route and completed two source-shaped passes")
        print("E-RUN: 0/2 complete cycles; one-pass probe: 2/2")
        print(f"envelope SHA-256: {digest}")
        return
    if expected_refusal not in result.stdout:
        raise SystemExit("canonical-E refusal does not match the pinned receipt")
    print("canonical E: loaded envelope and reported the pinned refusal")
    print("E-RUN: 0/0")
    print(f"envelope SHA-256: {digest}")


if __name__ == "__main__":
    main()
