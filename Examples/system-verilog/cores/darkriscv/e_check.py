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
    "a453663fe639176f1ff29d1aa3a1501dd1af0637551de625fe25c68b50f3f8c7":
        "decl 'REGS': unpacked array storage outside E (UnpackedDecl:memory)",
    "ddba565006335191c35955bd27c4c36ca134e57d8084864269b4a2f4fb77b96f":
        "decl 'REGS': unpacked array storage outside E (UnpackedDecl:memory)",
}

COREMEM_ENVELOPES = {
    "38b3c3253f79b006aac7a547d9c61fce31c86dfe26994a990ce324bd1ce321cf",
    "5fdb97fc8b4f663d7265e2d3128610319ab6f2cfc86576cb1cee519c78e44ccc",
    "ca8f0a92c7477ee9fd75f55966c122fa29400f8948a18ae361cc81a077077fc5",
    "a453663fe639176f1ff29d1aa3a1501dd1af0637551de625fe25c68b50f3f8c7",
    "ddba565006335191c35955bd27c4c36ca134e57d8084864269b4a2f4fb77b96f",
}


def main() -> None:
    envelope_text = os.environ.get("DARKRISCV_ENVELOPE")
    if not envelope_text:
        raise SystemExit("set DARKRISCV_ENVELOPE to the pinned envelope")
    envelope = Path(envelope_text).resolve()
    if not envelope.is_file():
        raise SystemExit(f"missing pinned envelope: {envelope.name}")
    digest = hashlib.sha256(envelope.read_bytes()).hexdigest()
    expected_refusal = ENVELOPE_REFUSAL.get(digest)
    if expected_refusal is None and digest not in COREMEM_ENVELOPES:
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
      | .ok (st2, _) => match d.prepareStep st2 (SvState.set (row 0) "CLK" (bits 1 1)) with
        | .ok (pre, before, after) => match d.runEdges d.env d.elems pre before after d.processes.toList with
          | .ok edge =>
            let committedStore := d.scalarEdge.commit edge.state.scalar edge.scalarQ
            let memory := edge.state.memory.commitNba edge.memoryQ
            let committed := d.normalizeScalar edge.state committedStore
            match memory with
            | some m =>
              "initial-ok\ntwo-pass-ok\nclock-prepare-ok\nclock-edges-ok\nclock-commit-built"
            | none => "initial-ok\ntwo-pass-ok\nclock-memory-commit-none"
          | .timeout => "initial-ok\ntwo-pass-ok\nclock-edges-timeout"
          | .unsupported m => "initial-ok\ntwo-pass-ok\nclock-edges-unsupported: " ++ m
        | .timeout => "initial-ok\ntwo-pass-ok\nclock-prepare-timeout"
        | .unsupported m => "initial-ok\ntwo-pass-ok\nclock-prepare-unsupported: " ++ m
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
    if digest in COREMEM_ENVELOPES:
        staged = 'initial-ok\\ntwo-pass-ok\\nclock-prepare-ok\\nclock-edges-ok\\nclock-commit-built'
        edge_wall = 'clock-edges-unsupported: AssignmentExpression:target:'
        if staged in result.stdout:
            print("canonical E: loaded one-rank memory route and completed two passes plus clock preparation, edge execution, and NBA commit construction")
            print("E-RUN: 0/2 complete cycles; staged clock probe: 4/4 stages")
        elif edge_wall in result.stdout:
            print("canonical E: loaded one-rank memory route; the first clock edge reaches the known assignment-target wall")
            print("E-RUN: 0/0 complete cycles; staged reset and preparation passed, edge execution refused")
        else:
            raise SystemExit("canonical-E staged clock probe did not complete or reach the pinned assignment-target wall")
        print(f"envelope SHA-256: {digest}")
        return
    if expected_refusal not in result.stdout:
        raise SystemExit("canonical-E refusal does not match the pinned receipt")
    print("canonical E: loaded envelope and reported the pinned refusal")
    print("E-RUN: 0/0")
    print(f"envelope SHA-256: {digest}")


if __name__ == "__main__":
    main()
