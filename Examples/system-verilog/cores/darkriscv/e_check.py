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
set_option maxRecDepth 100000 in
load_design_sv2 dark from "{path}"
#eval dark.pdesign.instantiateD2 [0] |>.hasUnsupported
#eval dark.pdesign.instantiateD2 [0] |>.processes.size
#eval dark.pdesign.instantiateD2 [0] |>.processes.toList.filterMap
  (fun p => match p with | .unsupported k t => some (k, t) | _ => none)
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
    if expected_refusal not in result.stdout:
        raise SystemExit("canonical-E refusal does not match the pinned receipt")
    print("canonical E: loaded envelope and reported the pinned refusal")
    print("E-RUN: 0/0")
    print(f"envelope SHA-256: {digest}")


if __name__ == "__main__":
    main()
