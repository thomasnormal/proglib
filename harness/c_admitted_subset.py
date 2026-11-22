#!/usr/bin/env python3
"""Render the C reader's admitted subset from survey and harness data.

The survey supplies corpus verdicts and exact first refusals.  The focused
case file supplies short source examples and expected outcomes.  This keeps
the page descriptive and regenerable rather than making it a second hand
maintained coverage table.
"""

from __future__ import annotations

import argparse
import json
from collections import Counter, defaultdict
from pathlib import Path


FAMILIES = (
    "integers and conversions",
    "enums",
    "control flow",
    "arrays",
    "pointers",
    "structs and layout forms",
    "unions",
    "bit-fields",
    "casts between pointers and integers",
    "string functions",
    "malloc/free",
    "variadics",
    "function pointers",
    "floating point",
)


def family_for_case(case: dict) -> str:
    """Assign a focused row to one reader-facing construct family."""
    text = " ".join(str(case.get(key, "")) for key in ("id", "source", "error"))
    low = text.lower()
    if "va-arg" in low or "va_" in low or "variadic" in low:
        return "variadics"
    if "function-pointer" in low or "function pointer" in low:
        return "function pointers"
    if "bitfield" in low or "bit-field" in low:
        return "bit-fields"
    if "union" in low:
        return "unions"
    if "enum" in low:
        return "enums"
    if any(word in low for word in ("malloc", "calloc", "free", "allocated-")):
        return "malloc/free"
    if any(word in low for word in ("switch", "goto", "order", "choose",
                                    "fallthrough", "static-local", "tentative")):
        return "control flow"
    if any(word in low for word in ("pointer-integer", "integer-to-pointer",
                                    "pointer-long", "pointer-unsigned-int",
                                    "ptr-int")):
        return "casts between pointers and integers"
    if "pointer" in low or "dangling" in low:
        return "pointers"
    if any(word in low for word in ("printf", "putchar", "puts", "strlen",
                                    "strcmp", "strncmp", "string", "strcpy")):
        return "string functions"
    if any(word in low for word in ("vla", "array", "filler", "subobject",
                                    "flexible", "sizeof-variable", "alignof")):
        return "arrays"
    if any(word in low for word in ("record", "aggregate", "layout",
                                    "anonymous", "struct")):
        return "structs and layout forms"
    if any(word in low for word in ("float", "floating", "double", "ieee",
                                    "long-double", "division")):
        return "floating point"
    if "sizeof" in low:
        return "arrays"
    return "integers and conversions"


def family_for_survey(row: dict) -> str:
    """Map a corpus row's static wall or refusal to a reader family."""
    text = " ".join(str(x) for x in (
        row.get("name", ""), row.get("detail", ""),
        row.get("dynamic_wall", ""), *row.get("static_walls", [])))
    return family_for_case({"id": text, "source": "", "error": ""})


def short_case(case: dict) -> str:
    source = " ".join(str(case.get("source", "")).split())
    if len(source) > 160:
        source = source[:157] + "..."
    expected = case.get("expect", "")
    detail = case.get("error") or case.get("expected_stdout") or ""
    suffix = f" — {detail}" if detail else ""
    return f"`{case.get('id', '?')}` ({expected}){suffix}: `{source}`"


def short_survey(row: dict) -> str:
    detail = row.get("detail") or row.get("dynamic_wall") or ""
    if len(detail) > 180:
        detail = detail[:177] + "..."
    suffix = f" — {detail}" if detail else ""
    return f"`{row.get('name', '?')}` ({row.get('verdict', '?')}){suffix}"


def render(survey: dict, cases: list[dict]) -> str:
    grouped_cases: dict[str, list[dict]] = defaultdict(list)
    for case in cases:
        grouped_cases[family_for_case(case)].append(case)
    grouped_rows: dict[str, list[dict]] = defaultdict(list)
    for row in survey.get("rows", []):
        grouped_rows[family_for_survey(row)].append(row)

    counts = Counter(row.get("verdict") for row in survey.get("rows", []))
    total = survey.get("total", 0)
    passed = counts.get("passed", 0)
    commit = survey.get("measured_commit", "unknown")
    measured = survey.get("measured_at_utc", "unknown")
    lines = [
        "# C admitted subset",
        "",
        "Generated from `docs/c-survey.json` and `harness/c_cases.json`.",
        "",
        f"The pinned GNU17 target currently has {passed}/{total} MATCH rows "
        f"in the active survey denominator. Measurement commit `{commit}`, "
        f"date `{measured}`.",
        "",
        "A focused row is an admitted example when its harness expectation is "
        "`match`. A `refuse` row documents the exact refusal boundary. Corpus "
        "failures are listed as known wrong answers and remain separate from "
        "refusals.",
        "",
    ]
    for family in FAMILIES:
        family_cases = grouped_cases.get(family, [])
        family_rows = grouped_rows.get(family, [])
        admitted = [case for case in family_cases if case.get("expect") == "match"]
        refused = [case for case in family_cases if case.get("expect") == "refuse"]
        wrong = [row for row in family_rows if row.get("verdict") == "failed"]
        corpus_refusals = [row for row in family_rows
                           if row.get("verdict", "").startswith("refused-")]
        lines += [f"## {family}", ""]
        if admitted:
            lines.append(f"- admitted: {short_case(admitted[0])}")
        else:
            lines.append("- admitted: no focused harness row")
        if refused:
            case = refused[0]
            lines.append(f"- refused: {short_case(case)}")
        elif corpus_refusals:
            lines.append(f"- refused: {short_survey(corpus_refusals[0])}")
        else:
            lines.append("- refused: no refusal row in the current inputs")
        if wrong:
            lines.append(f"- known wrong: {short_survey(wrong[0])}")
        else:
            lines.append("- known wrong: no scored failure in the current survey")
        lines.append("")
    return "\n".join(lines)


def self_test() -> int:
    survey = {"total": 2, "measured_commit": "test", "measured_at_utc": "today",
              "rows": [{"name": "x.c", "verdict": "passed", "detail": "",
                        "static_walls": ["type-layout"]},
                       {"name": "y.c", "verdict": "failed", "detail": "",
                        "static_walls": ["type-layout"]}]}
    cases = [{"id": "record-layout", "source": "struct S s;", "expect": "match"},
             {"id": "record-refusal", "source": "struct S s;", "expect": "refuse",
              "error": "no layout"}]
    page = render(survey, cases)
    checks = ("# C admitted subset" in page,
              "admitted:" in page, "refused:" in page, "known wrong:" in page,
              "`y.c` (failed)" in page)
    if not all(checks):
        raise SystemExit("c_admitted_subset --self-test: failed")
    print("c_admitted_subset --self-test: ok")
    return 0


def main() -> int:
    root = Path(__file__).resolve().parent.parent
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--survey", type=Path, default=root / "docs" / "c-survey.json")
    parser.add_argument("--cases", type=Path, default=root / "harness" / "c_cases.json")
    parser.add_argument("--output", type=Path, default=root / "docs" / "c-admitted-subset.md")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        return self_test()
    survey = json.loads(args.survey.read_text())
    cases = json.loads(args.cases.read_text())
    args.output.write_text(render(survey, cases))
    print(f"c_admitted_subset: wrote {args.output}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
