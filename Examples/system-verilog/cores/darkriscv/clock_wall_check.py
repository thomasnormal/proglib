#!/usr/bin/env python3
"""Check a fixed DarkRISCV clock run through canonical E.

The staged reset and edge receipt must pass before this probe attempts the
source-shaped clock run.  Each transition uses `fastStepCanonical`, whose
checked equality to `step` keeps the source-shaped canonical semantics while
avoiding repeated scalar-store reduction.  A bounded non-return is recorded
as an execution wall, while an explicit refusal remains distinguishable from
that wall.
"""

from __future__ import annotations

import hashlib
import os
from pathlib import Path
import subprocess
import sys
import tempfile


ENVELOPE_HASHES = {
    "ca7ba5a2e87ea6a1c2c0eb6b4975ac1a5c1787999241c4ba777adb25de82cd32",
    "120807c6e5a246cf634bbd2af593810cd00b7fafb75dd4bb8b385d7c3a1a753b",
    "0ce4d6079fc99f447a6ea82b4422de654192faba4495603b77a451705d19f9dc",
    "5fdb97fc8b4f663d7265e2d3128610319ab6f2cfc86576cb1cee519c78e44ccc",
    "ca8f0a92c7477ee9fd75f55966c122fa29400f8948a18ae361cc81a077077fc5",
    "a453663fe639176f1ff29d1aa3a1501dd1af0637551de625fe25c68b50f3f8c7",
    "ddba565006335191c35955bd27c4c36ca134e57d8084864269b4a2f4fb77b96f",
}
STAGED_CHECK = Path(__file__).with_name("e_check.py")
TIMEOUT_SECONDS = 180
CYCLE_COUNT = 1000


def bits(width: int, value: int) -> str:
    return f"LVec.ofNat {width} {value}"


def make_probe(envelope: Path) -> str:
    path = str(envelope).replace("\\", "\\\\").replace('"', '\\"')
    return f'''import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemFast
open LeanModels.Sv LeanModels.Sv.Kernel
set_option maxRecDepth 100000 in
load_design_sv2 dark from "{path}"
def bits (w n : Nat) := LVec.ofNat w n
def row (res : Nat) (clk : Nat) : SvState := [
  ("CLK", bits 1 clk), ("RES", bits 1 res), ("IRQ", bits 32 0),
  ("IDATA", bits 32 19), ("IDACK", bits 1 1), ("IBERR", bits 1 0),
  ("DATAI", bits 32 0), ("DDACK", bits 1 1), ("DBERR", bits 1 0)]
def runCycles (d : CoreMemDesign) : Nat → CoreMemState → Nat → Res String
  | 0, _, count => .ok (toString count ++ "-cycles-ok")
  | n + 1, st, count =>
      match d.fastStepCanonical st (row 0 0) with
      | .ok low =>
          match d.fastStepCanonical low (row 0 1) with
          | .ok high => runCycles d n high (count + 1)
          | .timeout => .timeout
          | .unsupported m => .unsupported (toString count ++ "-high-unsupported: " ++ m)
      | .timeout => .timeout
      | .unsupported m => .unsupported (toString count ++ "-low-unsupported: " ++ m)
#eval match PDesign.instantiateCoreMem dark.pdesign [0] with
| .ok d => match d.initialState with
  | .ok st => match d.stepOnePassTrace st (row 1 0) with
    | .ok (st1, _) => match d.stepOnePassTrace st1 (row 0 0) with
      | .ok (st2, _) => match d.fastStepCanonical st2 (row 0 1) with
        | .ok st3 => runCycles d {CYCLE_COUNT - 1} st3 1
        | .timeout => .timeout
        | .unsupported m => .unsupported ("clock-step-unsupported: " ++ m)
      | .timeout => .timeout
      | .unsupported m => .unsupported ("release-step-unsupported: " ++ m)
    | .timeout => .timeout
    | .unsupported m => .unsupported ("reset-step-unsupported: " ++ m)
  | .timeout => .timeout
  | .unsupported m => .unsupported ("initial-unsupported: " ++ m)
| .timeout => .timeout
| .unsupported m => .unsupported ("instantiate-unsupported: " ++ m)
'''


def run_staged(envelope: Path, repo: Path) -> None:
    result = subprocess.run(
        [sys.executable, str(STAGED_CHECK)],
        cwd=repo,
        env={**os.environ, "DARKRISCV_ENVELOPE": str(envelope)},
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
        timeout=TIMEOUT_SECONDS,
    )
    if result.returncode:
        raise SystemExit(result.stdout)
    expected = "staged clock probe: 4/4 stages"
    if expected not in result.stdout:
        raise SystemExit("staged receipt did not complete\n" + result.stdout)
    print(result.stdout, end="")


def run_clock_probe(envelope: Path, repo: Path) -> str:
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", prefix="darkriscv-clock-", delete=False
    ) as handle:
        handle.write(make_probe(envelope))
        script = Path(handle.name)
    try:
        try:
            result = subprocess.run(
                ["lake", "env", "lean", str(script)],
                cwd=repo,
                text=True,
                stdout=subprocess.PIPE,
                stderr=subprocess.STDOUT,
                check=False,
                timeout=TIMEOUT_SECONDS,
            )
        except subprocess.TimeoutExpired:
            return "clock-step-timeout"
    finally:
        script.unlink(missing_ok=True)
    if result.returncode:
        raise SystemExit(result.stdout)
    if "-cycles-ok" in result.stdout:
        return "cycles-ok"
    if "clock-step-timeout" in result.stdout or "Res.timeout" in result.stdout:
        return "cycle-timeout"
    if "clock-step-unsupported" in result.stdout or "-unsupported" in result.stdout:
        return "cycle-unsupported"
    raise SystemExit("clock probe produced no result\n" + result.stdout)


def main() -> int:
    envelope_text = os.environ.get("DARKRISCV_ENVELOPE")
    envelope = (Path(envelope_text).resolve() if envelope_text else Path(__file__).with_name("darkriscv.sv.json"))
    if not envelope.is_file():
        raise SystemExit(f"missing pinned envelope: {envelope.name}")
    digest = hashlib.sha256(envelope.read_bytes()).hexdigest()
    if digest not in ENVELOPE_HASHES:
        raise SystemExit(f"envelope SHA-256 {digest} is not a pinned receipt")

    repo = Path(__file__).resolve().parents[4]
    run_staged(envelope, repo)
    marker = run_clock_probe(envelope, repo)
    print(f"canonical E clock run: {marker}")
    print(f"bound: {TIMEOUT_SECONDS} seconds")
    print(f"envelope SHA-256: {digest}")
    if marker == "cycles-ok":
        print(f"E-RUN: {CYCLE_COUNT}/{CYCLE_COUNT} complete source-shaped rising-edge cycles")
    elif marker == "cycle-timeout":
        print(f"E-RUN: 0/{CYCLE_COUNT} complete source-shaped rising-edge cycles")
        print("execution wall: canonical E clock run did not return within the bound")
    else:
        print(f"E-RUN: 0/{CYCLE_COUNT} complete source-shaped rising-edge cycles")
        print("execution result: canonical E returned an explicit refusal")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
