#!/usr/bin/env python3
"""Bisect old survey MATCH losses against a fresh parser-envelope replay.

The audit joins receipts by their stable row name.  It does not inspect C
source text.  The fresh log is the current runner's result on envelopes made
by the approved extractor, so a row that returns to ``passed`` is an
instrument/envelope finding.  Every remaining row is assigned to its current
first wall and a recorded history boundary.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
from collections import Counter, defaultdict
from pathlib import Path


GROUPS = {
    "fresh-parser-envelope recovery": {
        "boundary": "fresh parser-native envelope replay",
        "first_commit": None,
        "route": "instrument: stale receipt/envelope path",
        "classification": "regression",
        "representatives": {
            "00025.c": "instrument boundary: stale receipt envelope",
            "20000519-1.c": "instrument boundary: stale receipt envelope",
            "931004-10.c": "instrument boundary: stale receipt envelope",
        },
    },
    "floating parser-native bits": {
        "boundary": "floating literal frontend price",
        "first_commit": "329189a93cbf8883b89170734a4a700b6f21248e",
        "route": "F7 shared floating-value/parser-bit work",
        "classification": "old MATCH was wrong (it relied on source-spelling floating values)",
        "representatives": {
            "00123.c": "329189a93 c: price floating literal frontend",
            "20000603-1.c": "329189a93 c: price floating literal frontend",
            "20001017-1.c": "329189a93 c: price floating literal frontend",
        },
    },
    "layout/aggregate binding": {
        "boundary": "declaration-identity layout join",
        "first_commit": "31f216ef733a84f362a90aebadb969cd376aba87",
        "route": "F1 parser-native layout and aggregate initialization",
        "classification": "regression for 00043.c and 20010116-1.c; old MATCH was wrong for 00124.c",
        "representatives": {
            "00043.c": "85dfb1421 f1: refuse anonymous layouts without identity",
            "00124.c": "before 08f21135d: pre-existing function-pointer layout wall",
            "20010116-1.c": "85dfb1421 f1: refuse anonymous layouts without identity",
        },
    },
    "declaration binding": {
        "boundary": "frontend declaration identity resolution",
        "first_commit": "f78ef6a5b",
        "route": "F1 declaration binding",
        "classification": "regression",
        "representatives": {
            "00024.c": "85dfb1421 f1: refuse anonymous layouts without identity",
            "00091.c": "85dfb1421 f1: refuse anonymous layouts without identity",
            "20000801-3.c": "85dfb1421 f1: refuse anonymous layouts without identity",
        },
    },
    "effective-type UB": {
        "boundary": "scalar effective-type check at access",
        "first_commit": "f6d5df37a86e8fe0e47802d86c69184318abc610",
        "route": "F2 effective-type compatibility",
        "classification": "regression",
        "representatives": {
            "20030903-1.c": "f6d5df37a f2: check scalar effective types at memory access",
            "minmaxcmp-1.c": "f6d5df37a f2: check scalar effective types at memory access",
            "postmod-1.c": "f6d5df37a f2: check scalar effective types at memory access",
        },
    },
    "bounds UB": {
        "boundary": "subobject pointer bounds check",
        "first_commit": "47568eb922eb36b7c1f9712bdb316152aabbf5e2",
        "route": "F2 object bounds",
        "classification": "old MATCH was wrong (the defined UB was previously executed)",
        "representatives": {
            "ptr-arith-1.c": "47568eb92 c: enforce subobject pointer bounds",
        },
    },
}


def portable_detail(detail: str) -> str:
    """Remove outside-cache prefixes while retaining the parser/model wall."""
    detail = " ".join(str(detail or "").split())
    detail = re.sub(r"[^ '\"()\t]+/src/", "src/", detail)
    return detail


def classify(verdict: str, detail: str) -> str:
    if verdict == "passed":
        return "fresh-parser-envelope recovery"
    if "floating literal lacks parser-native bits" in detail:
        return "floating parser-native bits"
    if verdict == "refused-ub" and "effectiveType" in detail:
        return "effective-type UB"
    if verdict == "refused-ub" and "outOfBounds" in detail:
        return "bounds UB"
    if "unbound declaration" in detail:
        return "declaration binding"
    if any(word in detail for word in
           ("layout", "size for element", "initialize aggregate", "union initializer")):
        return "layout/aggregate binding"
    raise ValueError(f"unclassified fresh wall: {verdict}: {detail}")


def parse_log(path: Path) -> dict[str, tuple[str, str]]:
    rows = {}
    for raw in path.read_text().splitlines():
        parts = raw.split("\t", 2)
        if len(parts) != 3:
            continue
        rows[parts[0]] = (parts[1], portable_detail(parts[2]))
    return rows


def portable_manifest_hash(path: Path) -> str:
    data = json.loads(path.read_text())

    def clean(value):
        if isinstance(value, dict):
            return {k: clean(v) for k, v in value.items()
                    if k not in ("cache", "envelope")}
        if isinstance(value, list):
            return [clean(v) for v in value]
        return value

    raw = json.dumps(clean(data), sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(raw).hexdigest()


def build(old_path: Path, receipt_path: Path, fresh_log: Path, fresh_manifest: Path | None = None):
    old = json.loads(old_path.read_text())
    receipt = json.loads(receipt_path.read_text())
    old_rows = {row["name"]: row for row in old.get("rows", [])}
    receipt_rows = {row["name"]: row for row in receipt.get("rows", [])}
    fresh = parse_log(fresh_log)
    names = sorted(name for name, row in old_rows.items()
                   if row.get("verdict") == "passed" and name in receipt_rows
                   and receipt_rows[name].get("verdict") != "passed")
    rows = []
    for name in names:
        current = fresh.get(name)
        if current is None:
            raise ValueError(f"fresh replay has no row for {name}")
        verdict, detail = current
        rows.append({
            "name": name,
            "old_verdict": old_rows[name].get("verdict"),
            "receipt_verdict": receipt_rows[name].get("verdict"),
            "receipt_detail": portable_detail(receipt_rows[name].get("detail", "")),
            "fresh_verdict": verdict,
            "fresh_detail": detail,
            "group": classify(verdict, detail),
            "receipt_agrees_with_fresh": (
                receipt_rows[name].get("verdict") == verdict and
                portable_detail(receipt_rows[name].get("detail", "")) == detail),
        })
    groups = []
    for name, info in GROUPS.items():
        selected = [row for row in rows if row["group"] == name]
        if not selected:
            continue
        pairs = Counter((row["receipt_verdict"], row["fresh_verdict"])
                        for row in selected)
        groups.append({
            "group": name,
            "rows": len(selected),
            "boundary": info["boundary"],
            "first_commit": info["first_commit"],
            "route": info["route"],
            "classification": info["classification"],
            "representatives": info["representatives"],
            "receipt_vs_fresh": [
                {"receipt": left, "fresh": right, "rows": count}
                for (left, right), count in sorted(pairs.items())
            ],
            "examples": [row["name"] for row in selected[:8]],
        })
    if sum(item["rows"] for item in groups) != len(rows):
        raise ValueError("group table does not cover every loss")
    result = {
        "schema": "c-drop-audit-0.1",
        "old_receipt": {"path_role": "committed survey", "measured_commit": old.get("measured_commit"),
                        "manifest_hash": old.get("manifest_hash"), "matched": old.get("counts", {}).get("passed"),
                        "rows": len(old.get("rows", []))},
        "receipt": {"path_role": "post-push survey", "measured_commit": receipt.get("measured_commit"),
                    "manifest_hash": receipt.get("manifest_hash"), "matched": receipt.get("counts", {}).get("passed"),
                    "rows": len(receipt.get("rows", []))},
        "fresh_replay": {
            "rows": len(fresh),
            "counts": dict(sorted(Counter(v for v, _ in fresh.values()).items())),
            **({"manifest_hash": portable_manifest_hash(fresh_manifest)} if fresh_manifest else {}),
        },
        "shared_old_match_losses": len(rows),
        "groups": groups,
        "rows": rows,
    }
    return result


def render(data):
    lines = [
        "# C survey drop audit",
        "",
        "Generated by `harness/c_drop_audit.py` from the committed survey, the post-push receipt, and a fresh parser-envelope replay.",
        "The 325 shared old-MATCH losses remain regression candidates until the fresh replay or a standard wall explains each row.",
        "",
        "| group | rows | representative bisect | classification | route |",
        "| --- | ---: | --- | --- | --- |",
    ]
    for item in data["groups"]:
        reps = "; ".join("`%s`: %s" % pair for pair in item["representatives"].items())
        lines.append("| `%s` | %d | %s | %s | %s |" %
                     (item["group"], item["rows"], reps, item["classification"], item["route"]))
    lines += [
        "",
        "## Measured split",
        "",
        "| outcome on fresh parser-native envelopes | rows |",
        "| --- | ---: |",
    ]
    for item in data["groups"]:
        lines.append("| `%s` | %d |" % (item["group"], item["rows"]))
    lines += ["", "## Per-group row names", ""]
    for item in data["groups"]:
        names = [row["name"] for row in data["rows"] if row["group"] == item["group"]]
        lines += ["### %s" % item["group"], "", ", ".join("`%s`" % name for name in names), ""]
    return "\n".join(lines)


def self_test():
    assert classify("passed", "") == "fresh-parser-envelope recovery"
    assert classify("refused-unsupported", "floating literal lacks parser-native bits") == "floating parser-native bits"
    assert classify("refused-ub", "MemFault.effectiveType") == "effective-type UB"
    assert classify("refused-unsupported", "no layout for declared type 'S'") == "layout/aggregate binding"
    assert portable_detail("/tmp/x/src/a.c:1: bad") == "src/a.c:1: bad"
    print("c_drop_audit --self-test: ok")
    return 0


def main(argv=None):
    ap = argparse.ArgumentParser()
    ap.add_argument("--old", type=Path)
    ap.add_argument("--receipt", type=Path)
    ap.add_argument("--fresh-log", type=Path)
    ap.add_argument("--fresh-manifest", type=Path)
    ap.add_argument("--json", type=Path)
    ap.add_argument("--page", type=Path)
    ap.add_argument("--self-test", action="store_true")
    args = ap.parse_args(argv)
    if args.self_test:
        return self_test()
    required = (args.old, args.receipt, args.fresh_log, args.json, args.page)
    if any(value is None for value in required):
        ap.error("--old, --receipt, --fresh-log, --json, and --page are required")
    data = build(args.old, args.receipt, args.fresh_log, args.fresh_manifest)
    args.json.write_text(json.dumps(data, indent=1, sort_keys=True) + "\n")
    args.page.write_text(render(data) + "\n")
    print(f"c_drop_audit: wrote {args.json} and {args.page}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
