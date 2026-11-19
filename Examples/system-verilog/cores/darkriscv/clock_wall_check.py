#!/usr/bin/env python3
"""Check the first clocked DarkRISCV transition through canonical E.

The staged reset and edge receipt must pass before this probe attempts the
full source-shaped step.  A bounded non-return is recorded as an execution
wall, while a returned value is printed for inspection and never relabelled
as a refusal.
"""

from __future__ import annotations

import hashlib
import os
from pathlib import Path
import subprocess
import sys
import tempfile


ENVELOPE_HASHES = {
    "ca8f0a92c7477ee9fd75f55966c122fa29400f8948a18ae361cc81a077077fc5",
    "a453663fe639176f1ff29d1aa3a1501dd1af0637551de625fe25c68b50f3f8c7",
}
STAGED_CHECK = Path(__file__).with_name("e_check.py")
TIMEOUT_SECONDS = 180


def bits(width: int, value: int) -> str:
    return f"LVec.ofNat {width} {value}"


def make_probe(envelope: Path) -> str:
    path = str(envelope).replace("\\", "\\\\").replace('"', '\\"')
    return f'''import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
open LeanModels.Sv LeanModels.Sv.Kernel
set_option maxRecDepth 100000 in
load_design_sv2 dark from "{path}"
def bits (w n : Nat) := LVec.ofNat w n
def row (res : Nat) (clk : Nat) : SvState := [
  ("CLK", bits 1 clk), ("RES", bits 1 res), ("IRQ", bits 32 0),
  ("IDATA", bits 32 19), ("IDACK", bits 1 1), ("IBERR", bits 1 0),
  ("DATAI", bits 32 0), ("DDACK", bits 1 1), ("DBERR", bits 1 0)]
#eval match PDesign.instantiateCoreMem dark.pdesign [0] with
| .ok d => match d.initialState with
  | .ok st => match d.stepOnePassTrace st (row 1 0) with
    | .ok (st1, _) => match d.stepOnePassTrace st1 (row 0 0) with
      | .ok (st2, _) => match d.stepOnePassTrace st2 (row 0 1) with
        | .ok _ => "clock-step-ok"
        | .timeout => "clock-step-timeout"
        | .unsupported m => "clock-step-unsupported: " ++ m
      | .timeout => "release-step-timeout"
      | .unsupported m => "release-step-unsupported: " ++ m
    | .timeout => "reset-step-timeout"
    | .unsupported m => "reset-step-unsupported: " ++ m
  | .timeout => "initial-timeout"
  | .unsupported m => "initial-unsupported: " ++ m
| .timeout => "instantiate-timeout"
| .unsupported m => "instantiate-unsupported: " ++ m
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
    for marker in ("clock-step-ok", "clock-step-timeout", "clock-step-unsupported"):
        if marker in result.stdout:
            return marker
    raise SystemExit("clock probe produced no result\n" + result.stdout)


def main() -> int:
    envelope_text = os.environ.get("DARKRISCV_ENVELOPE")
    if not envelope_text:
        raise SystemExit("set DARKRISCV_ENVELOPE to the pinned envelope")
    envelope = Path(envelope_text).resolve()
    if not envelope.is_file():
        raise SystemExit(f"missing pinned envelope: {envelope.name}")
    digest = hashlib.sha256(envelope.read_bytes()).hexdigest()
    if digest not in ENVELOPE_HASHES:
        raise SystemExit(f"envelope SHA-256 {digest} is not a pinned receipt")

    repo = Path(__file__).resolve().parents[4]
    run_staged(envelope, repo)
    marker = run_clock_probe(envelope, repo)
    print(f"canonical E first clock transition: {marker}")
    print(f"bound: {TIMEOUT_SECONDS} seconds")
    print(f"envelope SHA-256: {digest}")
    if marker == "clock-step-ok":
        print("E-RUN: 1/1 complete source-shaped clock transition")
    elif marker == "clock-step-timeout":
        print("E-RUN: 0/1 complete source-shaped clock transitions")
        print("execution wall: exact step did not return within the bound")
    else:
        print("E-RUN: 0/1 complete source-shaped clock transitions")
        print("execution result: canonical E returned an explicit refusal")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
