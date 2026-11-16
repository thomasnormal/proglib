#!/usr/bin/env python3
"""Check the parser-native unresolved-child refusal receipt."""
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[4]
HERE = Path(__file__).resolve().parent
ENV = HERE / "child_instance_wall.sv.json"


def main():
    source = "Examples/system-verilog/sem2/child_instance_wall/child_instance_wall.sv"
    envelope = "Examples/system-verilog/sem2/child_instance_wall/child_instance_wall.sv.json"
    subprocess.run([
        "python3", "extractors/sv/extract.py", "--top", "child_instance_wall",
        "-o", envelope, source],
        cwd=ROOT, check=True)
    out = subprocess.run([
        "python3", "harness/sv/refusal_census.py", "ordinary", str(ENV)],
        cwd=ROOT, check=True, text=True, stdout=subprocess.PIPE).stdout
    rows = [json.loads(line) for line in out.splitlines()]
    child = [r for r in rows
             if r.get("construct") == "UninstantiatedDefSymbol:UninstantiatedDef"]
    unknown = [r for r in rows if r.get("construct") == "SlangError:UnknownModule"]
    if len(child) != 1 or len(unknown) != 1:
        raise RuntimeError(f"unexpected refusal rows: {rows}")
    if child[0]["function"] != "GenItem.expand":
        raise RuntimeError(f"unexpected child refusal function: {child[0]}")
    print("ordinary census: UninstantiatedDefSymbol:UninstantiatedDef + SlangError:UnknownModule")
    print("no simulator oracle claimed for intentionally unresolved child")


if __name__ == "__main__":
    main()
