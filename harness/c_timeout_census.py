#!/usr/bin/env python3
"""Classify C model timeouts from parser-native envelopes.

The input log is the existing c-torture batch protocol.  For each timeout,
the manifest supplies the envelope produced by Clang's approved extractor;
this tool never opens or reparses C source.  A timeout is classified as
``loop`` when its envelope contains a ``WhileStmt``, ``ForStmt`` or
``DoStmt``, and ``straight-line`` otherwise.  Missing envelopes are reported
as ``unknown``.  Recursive calls are deliberately not inferred from names:
the envelope's declaration identity is the authority, and a timeout census
must not reconstruct call binding from spellings.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter
from pathlib import Path

from c_torture_score import parse


LOOPS = {"WhileStmt", "ForStmt", "DoStmt"}


def walk(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def classify(env):
    nodes = list(walk(env.get("translation_unit", {})))
    if any(n.get("kind") in LOOPS for n in nodes):
        return "loop"
    return "straight-line"


def build(manifest_path, log_path):
    manifest = json.loads(Path(manifest_path).read_text())
    by_name = {x.get("name"): x for x in manifest.get("tests", [])}
    timeouts = {
        name for name, verdict, _ in parse(Path(log_path).read_text().splitlines())
        if verdict == "timeout"
    }
    rows = []
    for name in sorted(timeouts):
        entry = by_name.get(name, {})
        env_path = entry.get("envelope")
        if not env_path or not Path(env_path).is_file():
            kind = "unknown"
        else:
            kind = classify(json.loads(Path(env_path).read_text()))
        rows.append({"name": name, "classification": kind})
    return {"schema": "c-timeout-census-0.1", "rows": rows,
            "counts": dict(sorted(Counter(x["classification"] for x in rows).items()))}


def self_test():
    env = {"translation_unit": {"decls": [{"kind": "FunctionDecl", "name": "main",
        "body": {"kind": "CompoundStmt", "body": [{"kind": "WhileStmt"}]}}]}}
    if classify(env) != "loop":
        raise SystemExit("c_timeout_census --self-test: loop classification failed")
    env["translation_unit"]["decls"][0]["body"] = {"kind": "CompoundStmt"}
    if classify(env) != "straight-line":
        raise SystemExit("c_timeout_census --self-test: straight-line classification failed")
    print("c_timeout_census --self-test: ok")


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("manifest", nargs="?")
    ap.add_argument("log", nargs="?")
    ap.add_argument("--json", help="write the census JSON here")
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args()
    if args.self_test:
        self_test(); return 0
    if not args.manifest or not args.log:
        ap.error("manifest and log are required unless --self-test is used")
    data = build(args.manifest, args.log)
    if args.json:
        Path(args.json).write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")
    print(json.dumps(data["counts"], sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
