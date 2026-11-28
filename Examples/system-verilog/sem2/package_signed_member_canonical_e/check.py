#!/usr/bin/env python3
"""Differential receipt for package-array aggregate-member constants."""
import json
import shutil
import subprocess
import tempfile
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
TOP = "package_unsigned_member_canonical_e"
POSITIVE = HERE / f"{TOP}.sv"
POSITIVE_ENV = HERE / f"{TOP}.sv.json"
SIGNED = HERE / "package_signed_member_canonical_e.sv"
SIGNED_ENV = HERE / "package_signed_member_canonical_e.sv.json"
EXPECTED = ["00000004", "00000006"]


def run(cmd, cwd=ROOT):
    proc = subprocess.run(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                          stderr=subprocess.STDOUT, timeout=180)
    if proc.returncode:
        raise RuntimeError(proc.stdout)
    return proc.stdout


def has_signed_refusal(node):
    if isinstance(node, dict):
        if (node.get("kind") == "Unsupported" and
                "ConversionExpression:Explicit" in node.get("sv_kind", "")):
            return True
        return any(has_signed_refusal(value) for value in node.values())
    if isinstance(node, list):
        return any(has_signed_refusal(value) for value in node)
    return False


def rows(text):
    for line in text.splitlines():
        if line.startswith("ROW "):
            fields = line.split()
            return [fields[1].split("=", 1)[1], fields[2].split("=", 1)[1]]
    return []


def main():
    with tempfile.NamedTemporaryFile(suffix=".json") as fresh:
        run(["python3", "extractors/sv/extract.py", "--top", TOP, "-o",
             fresh.name, str(POSITIVE.relative_to(ROOT))])
        if Path(fresh.name).read_bytes() != POSITIVE_ENV.read_bytes():
            raise RuntimeError("positive envelope is stale")
    with tempfile.NamedTemporaryFile(suffix=".json") as fresh:
        run(["python3", "extractors/sv/extract.py", "--top",
             "package_signed_member_canonical_e", "-o", fresh.name,
             str(SIGNED.relative_to(ROOT))])
        if Path(fresh.name).read_bytes() != SIGNED_ENV.read_bytes():
            raise RuntimeError("signed envelope is stale")
    if not has_signed_refusal(json.loads(SIGNED_ENV.read_text())):
        raise RuntimeError("signed member did not retain a loud refusal")
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    print("canonical E: unsigned K=0/K=1 rows MATCH")
    print("canonical extractor: signed member retains ConversionExpression:Explicit refusal")
    if shutil.which("xrun"):
        with tempfile.TemporaryDirectory(prefix="sv-package-member-") as work:
            out = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top",
                       f"{TOP}_tb", str(POSITIVE),
                       str(HERE / f"{TOP}_tb.sv")], Path(work))
        if rows(out) != EXPECTED:
            raise RuntimeError(f"Xcelium: {rows(out)} != {EXPECTED}")
        print("Xcelium: two positive rows MATCH")
    else:
        print("SKIP: Xcelium unavailable; canonical-E rows still checked")


if __name__ == "__main__":
    main()
