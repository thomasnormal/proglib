#!/usr/bin/env python3
"""Collect all extractor and ordinary-route refusals as JSON Lines.

The extractor path delegates to Slang through ``extract.py --census``.  The
ordinary path delegates admission to the Lean runner, which calls the same
PDesign instantiation and guard functions as ``load_design_sv2``.  This file
only joins source spans from the retained envelope; it contains no SV rules.
"""

import argparse
import json
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EXTRACT = ROOT / "extractors" / "sv" / "extract.py"
RUNNER = ROOT / "harness" / "sv" / "refusal_census.lean"


def envelope_rows(path):
    rows = []

    def walk(node):
        if isinstance(node, dict):
            if node.get("kind") == "Unsupported":
                span = node.get("span") or {}
                rows.append((node.get("sv_kind", "Unsupported"),
                             node.get("text", ""), span.get("line"),
                             span.get("col")))
            for value in node.values():
                walk(value)
        elif isinstance(node, list):
            for value in node:
                walk(value)

    walk(json.loads(Path(path).read_text()))
    return rows


def enrich(row, spans):
    if row.get("line") is not None:
        return row
    construct = row.get("construct", "")
    message = row.get("message", "")
    for kind, text, line, col in spans:
        if kind == construct and (not message or message in text or text in message):
            row["line"], row["column"] = line, col
            return row
    for kind, text, line, col in spans:
        if kind == construct:
            row["line"], row["column"] = line, col
            return row
    return row


def run_extract(args):
    cmd = [sys.executable, str(EXTRACT), "--census", "--top", args.top,
           *args.sources]
    if args.retain_proc_rewrites:
        cmd.insert(2, "--retain-proc-rewrites")
    if args.out:
        cmd += ["-o", args.out]
    result = subprocess.run(cmd, cwd=ROOT, text=True, capture_output=True)
    sys.stderr.write(result.stderr)
    for line in result.stdout.splitlines():
        try:
            row = json.loads(line)
        except json.JSONDecodeError:
            continue
        if row.get("stage") == "extractor":
            print(json.dumps(row, sort_keys=True))
    return result.returncode


def run_ordinary(args):
    cmd = ["lake", "env", "lean", "--run", str(RUNNER), args.envelope]
    result = subprocess.run(cmd, cwd=ROOT, text=True, capture_output=True)
    sys.stderr.write(result.stderr)
    spans = envelope_rows(args.envelope)
    count = 0
    for line in result.stdout.splitlines():
        try:
            row = json.loads(line)
        except json.JSONDecodeError:
            continue
        if row.get("stage") == "ordinary":
            print(json.dumps(enrich(row, spans), sort_keys=True))
            count += 1
    if result.returncode == 0 and count == 0:
        print(json.dumps({"stage": "summary", "refusals": 0}, sort_keys=True))
    return result.returncode


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest="mode", required=True)
    extract = sub.add_parser("extract")
    extract.add_argument("--top", required=True)
    extract.add_argument("-o", "--out")
    extract.add_argument("--retain-proc-rewrites", action="store_true",
                         help="retain source-shaped procedural rewrites")
    extract.add_argument("sources", nargs="+")
    ordinary = sub.add_parser("ordinary")
    ordinary.add_argument("envelope")
    args = parser.parse_args(argv)
    return run_extract(args) if args.mode == "extract" else run_ordinary(args)


if __name__ == "__main__":
    raise SystemExit(main())
