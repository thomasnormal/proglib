#!/usr/bin/env python3
"""Check the pinned SERV envelope through canonical E."""

from __future__ import annotations

import hashlib
import os
from pathlib import Path
import subprocess
import tempfile


ENVELOPE_SHA256 = {
    "ea713d68c00b6bc3cc4e892de56bf1ccc74d1ba2dcc9dc30abb9a317c64c7a64",
    "df120564f32fd92c2c45c980ae9d6602ee53a820440b39baeaec5648a39bc875",
}
EXPECTED_REFUSAL = "parameter 'RF_WIDTH' default: Constant:untyped-width"


def main() -> None:
    envelope_text = os.environ.get("SERV_ENVELOPE")
    if not envelope_text:
        raise SystemExit("set SERV_ENVELOPE to the pinned envelope")
    envelope = Path(envelope_text).resolve()
    if not envelope.is_file():
        raise SystemExit(f"missing pinned envelope: {envelope.name}")
    digest = hashlib.sha256(envelope.read_bytes()).hexdigest()
    if digest not in ENVELOPE_SHA256:
        raise SystemExit(f"envelope SHA-256 {digest} is not a pinned receipt")

    path = str(envelope).replace("\\", "\\\\").replace('"', '\\"')
    lean_source = f'''import LeanModels.Sv.Ingest2
set_option maxRecDepth 100000 in
load_design_sv2 serv from "{path}"
'''
    repo = Path(__file__).resolve().parents[4]
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", prefix="serv-e-", delete=False
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
