#!/usr/bin/env python3
"""Price the survey's sole vector-layout wall from parser observations.

The source files are selected by the committed survey.  Clang's approved
record-layout probe is run unchanged on each source and the report carries its
TypeLayout records without interpreting a type spelling.
"""

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
WALL = "unsupported:no layout for declared type 'V'"


def extract(source, clang, plugin, source_name):
    output = Path("/tmp") / ("c-vector-layout-" + hashlib.sha256(str(source).encode()).hexdigest() + ".json")
    env = os.environ.copy()
    env["LEAN_C_CLANG"] = clang
    env["LEAN_C_RECORD_LAYOUT_PLUGIN"] = plugin
    try:
        result = subprocess.run(
            [sys.executable, str(ROOT / "extractors/c/extract.py"), str(source),
             "--source-name", source_name, "-o", str(output)],
            cwd=ROOT, env=env, capture_output=True, text=True, check=False)
        if result.returncode:
            raise RuntimeError(result.stderr[-2000:] or result.stdout[-2000:])
        return json.loads(output.read_text())
    finally:
        output.unlink(missing_ok=True)


def price(survey, roots, clang, plugin):
    rows = [row for row in survey.get("rows", []) if row.get("dynamic_wall") == WALL]
    priced = []
    for row in rows:
        source = Path(roots[row["corpus"]]) / row["name"]
        envelope = extract(source, clang, plugin, row["corpus"] + ":" + row["name"])
        layouts = envelope.get("type_layouts")
        if not isinstance(layouts, list) or not layouts:
            raise RuntimeError("no parser-native TypeLayout records for " + row["name"])
        priced.append({
            "corpus": row["corpus"], "name": row["name"],
            "sha256": row.get("sha256"),
            "type_layouts": layouts,
        })
    return {
        "schema": "c-vector-layout-price-0.1",
        "wall": WALL,
        "survey_commit": survey.get("measured_commit"),
        "survey_measured_at_utc": survey.get("measured_at_utc"),
        "candidate_rows": len(rows),
        "all_rows_joined": len(priced) == len(rows),
        "rows": priced,
        "interpretation": (
            "The nine files are the survey's sole dynamic V-layout wall. "
            "Every candidate has parser-native TypeLayout observations from "
            "the pinned Clang probe. The report prices the layout boundary only "
            "and claims no vector semantics or corpus flip."
        ),
    }


def render(report):
    lines = ["# C parser-native vector layout price", "",
             "- survey commit: `%s`" % report.get("survey_commit", ""),
             "- candidate files: **%d**" % report.get("candidate_rows", 0),
             "- all rows joined: **%s**" % report.get("all_rows_joined", False), "",
             "| corpus | file | TypeLayout records | sizes / alignments |",
             "| --- | --- | ---: | --- |"]
    for row in report.get("rows", []):
        facts = ", ".join("%s/%s" % (x.get("size_bytes"), x.get("alignment_bytes"))
                           for x in row.get("type_layouts", []))
        lines.append("| `%s` | `%s` | %d | `%s` |" %
                     (row["corpus"], row["name"], len(row["type_layouts"]), facts))
    lines += ["", report.get("interpretation", ""), ""]
    return "\n".join(lines)


def self_test():
    report = {
        "candidate_rows": 1, "all_rows_joined": True,
        "rows": [{"corpus": "c", "name": "x.c", "type_layouts":
                  [{"size_bytes": 16, "alignment_bytes": 16}]}]}
    if "16/16" not in render(report):
        raise SystemExit("c_vector_layout_price --self-test: rendering failed")
    print("c_vector_layout_price --self-test: ok")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--input", default=str(ROOT / "docs/c-survey.json"))
    parser.add_argument("--json")
    parser.add_argument("--page")
    parser.add_argument("--clang", default=os.environ.get("LEAN_C_CLANG", "clang"))
    parser.add_argument("--plugin", required=False)
    parser.add_argument("--c1-root", required=False)
    parser.add_argument("--c2-root", required=False)
    parser.add_argument("--c3-root", required=False)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return 0
    if not args.plugin or not args.c1_root or not args.c2_root or not args.c3_root:
        parser.error("--plugin and all corpus roots are required")
    roots = {"gcc.c-torture/execute": args.c1_root,
             "c-testsuite/single-exec": args.c2_root,
             "gcc.c23-run": args.c3_root}
    report = price(json.loads(Path(args.input).read_text()), roots, args.clang, args.plugin)
    if args.json:
        Path(args.json).write_text(json.dumps(report, indent=1, sort_keys=True) + "\n")
    if args.page:
        Path(args.page).write_text(render(report))
    print("c_vector_layout_price: %d candidate rows, all joined" % report["candidate_rows"])


if __name__ == "__main__":
    raise SystemExit(main())
