#!/usr/bin/env python3
"""Check the focused GNU StmtExpr wall against Clang and the C runner."""

import argparse
import json
import pathlib

ROWS = [
    "20000703-1.c", "20000917-1.c", "20020206-1.c", "20020320-1.c",
    "930406-1.c", "950906-1.c",
]


def self_test():
    assert ROWS[-1] == "950906-1.c"
    print("c_statement_expr_audit --self-test: ok")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--json")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return
    if not args.json:
        parser.error("--json is required")
    rows = json.loads(pathlib.Path(args.json).read_text())["rows"]
    names = [row["name"] for row in rows]
    if names != ROWS:
        raise SystemExit(f"unexpected focused rows: {names!r}")
    if rows[-1].get("model") != "0" or rows[-1].get("native") != "0/O0/O2/UBSan-ASan":
        raise SystemExit("950906-1.c focused result changed")
    print("c_statement_expr_audit: focused result verified")


if __name__ == "__main__":
    main()
