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
import re

ROOT = Path(__file__).resolve().parent.parent
WALL = "unsupported:no layout for declared type 'V'"


def sanitize_type_paths(value, corpus, name):
    """Keep parser facts while replacing Clang's absolute source path.

    Clang includes the spelling location in anonymous aggregate type names.
    Reports are public artifacts, so that location must use the repository
    relative corpus/name pair rather than the checkout path used for a run.
    """
    if isinstance(value, str):
        return re.sub(r" at /[^:\"]+/(?:src/)?[^:\":]+:(\d+:\d+)",
                      rf" at {corpus}/{name}:\1", value)
    if isinstance(value, list):
        return [sanitize_type_paths(x, corpus, name) for x in value]
    if isinstance(value, dict):
        return {k: sanitize_type_paths(v, corpus, name) for k, v in value.items()}
    return value


def sanitize_report(report):
    for row in report.get("rows", []):
        row["type_layouts"] = sanitize_type_paths(
            row.get("type_layouts", []), row["corpus"], row["name"])
    return report


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


def price(survey, roots, clang, plugin, wall=WALL):
    walls = [wall] if isinstance(wall, str) else list(wall)
    rows = [row for row in survey.get("rows", []) if row.get("dynamic_wall") in walls]
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
            "type_layouts": sanitize_type_paths(layouts, row["corpus"], row["name"]),
        })
    return {
        "schema": "c-vector-layout-price-0.1",
        "wall": walls[0] if len(walls) == 1 else "multiple",
        "walls": walls,
        "survey_commit": survey.get("measured_commit"),
        "survey_measured_at_utc": survey.get("measured_at_utc"),
        "candidate_rows": len(rows),
        "all_rows_joined": len(priced) == len(rows),
        "rows": priced,
        "interpretation": (
            "The selected files are the survey's sole dynamic layout wall. "
            "Every candidate has parser-native TypeLayout observations from "
            "the pinned Clang probe. The report prices the layout boundary only "
            "and claims no semantics or corpus flip."
        ),
    }


def render(report):
    lines = ["# C parser-native layout price", "",
             "- survey commit: `%s`" % report.get("survey_commit", ""),
             "- dynamic walls: %s" % ", ".join("`%s`" % wall for wall in report.get("walls", [report.get("wall", "")])),
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
    parser.add_argument("--wall", action="append")
    parser.add_argument("--c1-root", required=False)
    parser.add_argument("--c2-root", required=False)
    parser.add_argument("--c3-root", required=False)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--rewrite-existing", nargs="+", metavar="JSON",
                        help="sanitize existing reports in place")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return 0
    if args.rewrite_existing:
        for report_path in args.rewrite_existing:
            path = Path(report_path)
            path.write_text(json.dumps(sanitize_report(json.loads(path.read_text())),
                                       indent=1, sort_keys=True) + "\n")
        print("c_vector_layout_price: sanitized %d existing reports" % len(args.rewrite_existing))
        return 0
    if not args.plugin or not args.c1_root or not args.c2_root or not args.c3_root:
        parser.error("--plugin and all corpus roots are required")
    roots = {"gcc.c-torture/execute": args.c1_root,
             "c-testsuite/single-exec": args.c2_root,
             "gcc.c23-run": args.c3_root}
    report = price(json.loads(Path(args.input).read_text()), roots, args.clang,
                   args.plugin, args.wall or WALL)
    if args.json:
        Path(args.json).write_text(json.dumps(report, indent=1, sort_keys=True) + "\n")
    if args.page:
        Path(args.page).write_text(render(report))
    print("c_vector_layout_price: %d candidate rows, all joined" % report["candidate_rows"])


if __name__ == "__main__":
    raise SystemExit(main())
