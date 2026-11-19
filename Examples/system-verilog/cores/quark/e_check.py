#!/usr/bin/env python3
"""Check the pinned Quark envelope through canonical E."""

from __future__ import annotations

import hashlib
import os
from pathlib import Path
import subprocess
import tempfile


ENVELOPE_SHA256 = {
    "644b5ee318e42fe3362798172495e500cf001efeeded0b689eea4d7c9a355ccb",
    "9a97d6736c30221e580f898673adb6fcaa49931d24eec1494d006e040bdfc1ce",
    "b26f0bd9ca5cb9a40838bb7719ae9877876d572f02de076d52d4d9dc62c1efdc",
    "ec5e14623631bce248ff56341e425721cd1242408a3279fd120c694e15fa74c2",
    "19e757d78a76214d9b4e56a3fbfcd7ee98c303936d7d9f8a1a4dcdd8db72c519",
    "7c2011727dde42093d232b268f0c33d892abbd8dbb7fe1604a7ad593cd156cf6",
}
EXPECTED_REFUSAL = "localparam 'FETCH_INSTR': Constant:untyped-width"


def main() -> None:
    envelope_text = os.environ.get("QUARK_ENVELOPE")
    if not envelope_text:
        raise SystemExit("set QUARK_ENVELOPE to the pinned envelope")
    envelope = Path(envelope_text).resolve()
    if not envelope.is_file():
        raise SystemExit(f"missing pinned envelope: {envelope.name}")
    digest = hashlib.sha256(envelope.read_bytes()).hexdigest()
    if digest not in ENVELOPE_SHA256:
        raise SystemExit(f"envelope SHA-256 {digest} is not a pinned receipt")

    path = str(envelope).replace("\\", "\\\\").replace('"', '\\"')
    lean_source = f'''import LeanModels.Sv.Ingest2
set_option maxRecDepth 100000 in
load_design_sv2 femto from "{path}"
'''
    repo = Path(__file__).resolve().parents[4]
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", prefix="quark-e-", delete=False
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
    if result.returncode == 0 or EXPECTED_REFUSAL not in result.stdout:
        raise SystemExit("canonical-E loader result does not match the pinned refusal")
    print("canonical E: refused the envelope at the pinned differential wall")
    print("E-RUN: 0/0")
    print(f"envelope SHA-256: {digest}")


if __name__ == "__main__":
    main()
