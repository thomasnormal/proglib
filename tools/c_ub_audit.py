#!/usr/bin/env python3
"""Bounded, resumable sanitizer qualification for the C survey's UB rows.

The survey names the rows and the corpus roots supply the unchanged sources.
Each native executable is run through ``timeout 1``.  A JSON checkpoint is
written after every phase, so a slow or killed row cannot make the controller
lose the rows that were already qualified.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from collections import Counter
from pathlib import Path
import re
import shutil
import subprocess


PHASES = ("o0", "o2", "san")
SCHEMA = "c-ub-audit-1"
STATE_SCHEMA = "c-ub-audit-state-1"
UB_MARKERS = ("runtime error:", "UndefinedBehaviorSanitizer", "AddressSanitizer")


def read_json(path: Path):
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, value) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(path.name + ".tmp")
    temporary.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n",
                         encoding="utf-8")
    temporary.replace(path)


def survey_digest(survey) -> str:
    rows = [(row.get("corpus"), row.get("name"), row.get("sha256"),
             row.get("detail"))
            for row in survey.get("rows", [])
            if row.get("verdict") == "refused-ub"]
    raw = json.dumps(rows, sort_keys=True, separators=(",", ":")).encode()
    return hashlib.sha256(raw).hexdigest()


def source_for(root: Path, name: str) -> Path:
    direct = root / name
    if direct.is_file():
        return direct
    candidates = list(root.glob("*/src/" + name))
    if len(candidates) == 1:
        return candidates[0]
    if not candidates:
        raise FileNotFoundError(f"source not found for {name} under {root}")
    raise RuntimeError(f"multiple sources found for {name} under {root}")


def portable_detail(detail: str) -> str:
    detail = " ".join(str(detail or "").split())
    detail = re.sub(r"[^ \t\n]+/(?:src|tests|gcc)/", "", detail)
    detail = re.sub(r"/(?:scratch|tmp|home|var)/[^ \t\n]+", "<path>", detail)
    return detail[-600:]


def invoke(command, timeout_seconds: float | None = None):
    try:
        result = subprocess.run(command, capture_output=True, text=True,
                                timeout=timeout_seconds)
        return {"returncode": result.returncode,
                "stdout": portable_detail(result.stdout),
                "stderr": portable_detail(result.stderr),
                "timeout": False}
    except subprocess.TimeoutExpired as error:
        return {"returncode": 124, "stdout": portable_detail(error.stdout or ""),
                "stderr": portable_detail(error.stderr or ""), "timeout": True}


def run_phase(clang: str, source: Path, output: Path, phase: str,
              compile_timeout: float) -> dict:
    common = [clang, "--no-default-config", "-std=c23", "-g",
              "-D_FORTIFY_SOURCE=0", "-fno-strict-aliasing"]
    if phase == "o0":
        flags = ["-O0"]
    elif phase == "o2":
        flags = ["-O2"]
    elif phase == "san":
        flags = ["-O0", "-fsanitize=undefined,address",
                 "-fno-sanitize-recover=all"]
    else:
        raise ValueError(phase)
    compiled = invoke(common + flags + [str(source), "-o", str(output)],
                      compile_timeout)
    if compiled["timeout"]:
        return {"status": "compile-timeout", **compiled}
    if compiled["returncode"] != 0:
        return {"status": "compile-failed", **compiled}
    # The one-second wall is the qualification boundary.  ``timeout`` is a
    # separate process so an infinite test cannot hold the Python controller.
    ran = invoke(["timeout", "--kill-after=1s", "1s", str(output)], 3.0)
    if ran["timeout"]:
        return {"status": "controller-timeout", **ran}
    if ran["returncode"] in (124, 137):
        return {"status": "controller-timeout", **ran}
    return {"status": "run", **ran}


def evidence(row: dict) -> str:
    san = row.get("phases", {}).get("san")
    if not san:
        return "incomplete"
    if san["status"] in ("compile-failed", "compile-timeout"):
        return "oracle-no-result"
    if san["status"] == "controller-timeout":
        return "timeout"
    if san.get("returncode") == 0:
        return "clean-no-ub-witness"
    if any(marker in san.get("stderr", "") for marker in UB_MARKERS):
        return "sanitizer-witness"
    return "nonzero-without-sanitizer-diagnostic"


def select_rows(survey) -> list[dict]:
    return [{"corpus": row["corpus"], "name": row["name"],
             "model": row.get("detail", ""), "sha256": row.get("sha256"),
             "phases": {}}
            for row in survey.get("rows", [])
            if row.get("verdict") == "refused-ub"]


def validate_state(state, survey_rows, digest):
    if state.get("schema") != STATE_SCHEMA:
        raise ValueError("state has an unsupported schema")
    if state.get("survey_digest") != digest:
        raise ValueError("state belongs to a different UB-row survey")
    expected = [(row["corpus"], row["name"]) for row in survey_rows]
    actual = [(row["corpus"], row["name"]) for row in state.get("rows", [])]
    if actual != expected:
        raise ValueError("state row set does not match the survey")


def render(receipt: dict) -> str:
    counts = Counter(row.get("evidence", "incomplete") for row in receipt["rows"])
    lines = [
        "# C refused-UB qualification",
        "",
        "Generated by `tools/c_ub_audit.py` from the current survey's refused-UB rows.",
        "Every native executable has a one-second `timeout` wall. A clean sanitizer run is recorded as no UB witness.",
        "",
        f"Status: **{receipt['status']}** ({len(receipt['rows'])}/{receipt['total']} rows complete)",
        "",
        "| evidence | rows |",
        "| --- | ---: |",
    ]
    for key in sorted(counts):
        lines.append(f"| `{key}` | {counts[key]} |")
    lines += ["", "| corpus | row | model refusal | evidence |", "| --- | --- | --- | --- |"]
    for row in receipt["rows"]:
        lines.append(f"| `{row['corpus']}` | `{row['name']}` | `{row['model']}` | `{row.get('evidence', 'incomplete')}` |")
    return "\n".join(lines) + "\n"


def self_test() -> int:
    assert portable_detail("/x/src/a.c:1: runtime error: bad") == "a.c:1: runtime error: bad"
    assert portable_detail("/scratch/user/cache/a.c:1: bad") == "<path> bad"
    assert evidence({"phases": {"san": {"status": "run", "returncode": 1,
                                          "stderr": "runtime error: overflow"}}}) == "sanitizer-witness"
    assert evidence({"phases": {"san": {"status": "run", "returncode": 0,
                                          "stderr": ""}}}) == "clean-no-ub-witness"
    assert evidence({"phases": {"san": {"status": "controller-timeout"}}}) == "timeout"
    print("c_ub_audit --self-test: ok")
    return 0


def parse_roots(values):
    roots = {}
    for value in values:
        if "=" not in value:
            raise ValueError("--root expects CORPUS=PATH")
        corpus, path = value.split("=", 1)
        roots[corpus] = Path(path)
    return roots


def main(argv=None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--survey", type=Path, default=Path("docs/c-survey.json"))
    parser.add_argument("--state", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--page", type=Path)
    parser.add_argument("--work-dir", type=Path, required=False)
    parser.add_argument("--root", action="append", default=[], metavar="CORPUS=PATH")
    parser.add_argument("--clang", default=os.environ.get("LEAN_C_CLANG", "clang"))
    parser.add_argument("--max-rows", type=int, default=None)
    parser.add_argument("--compile-timeout", type=float, default=60.0)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(argv)
    if args.self_test:
        return self_test()
    if not args.state or not args.output or not args.page or not args.work_dir:
        parser.error("--state, --output, --page and --work-dir are required")
    roots = parse_roots(args.root)
    survey = read_json(args.survey)
    selected = select_rows(survey)
    digest = survey_digest(survey)
    if args.state.exists():
        state = read_json(args.state)
        validate_state(state, selected, digest)
    else:
        state = {"schema": STATE_SCHEMA, "survey_digest": digest,
                 "rows": selected, "next_index": 0}
        write_json(args.state, state)
    # Older scratch checkpoints recorded the timeout command's 124 as a
    # regular run.  Normalize that representation before rendering a receipt.
    for row in state["rows"]:
        for phase in row.get("phases", {}).values():
            if phase.get("status") == "run" and phase.get("returncode") in (124, 137):
                phase["status"] = "controller-timeout"
    args.work_dir.mkdir(parents=True, exist_ok=True)
    clang_path = shutil.which(args.clang) or args.clang
    completed_this_run = 0
    while state["next_index"] < len(state["rows"]):
        if args.max_rows is not None and completed_this_run >= args.max_rows:
            break
        row = state["rows"][state["next_index"]]
        source = source_for(roots[row["corpus"]], row["name"])
        if row.get("sha256"):
            digest_source = hashlib.sha256(source.read_bytes()).hexdigest()
            if digest_source != row["sha256"]:
                raise ValueError(f"source hash mismatch for {row['name']}")
        stem = row["corpus"].replace("/", "_") + "__" + row["name"].replace("/", "_")
        for phase in PHASES:
            if phase in row["phases"]:
                continue
            binary = args.work_dir / (stem + "__" + phase)
            row["phases"][phase] = run_phase(clang_path, source, binary, phase,
                                               args.compile_timeout)
            write_json(args.state, state)
        row["evidence"] = evidence(row)
        state["next_index"] += 1
        completed_this_run += 1
        write_json(args.state, state)
    receipt = {"schema": SCHEMA, "survey_digest": digest,
               "status": "complete" if state["next_index"] == len(state["rows"])
               else "partial", "total": len(state["rows"]),
               "completed": state["next_index"], "rows": state["rows"]}
    write_json(args.output, receipt)
    args.page.parent.mkdir(parents=True, exist_ok=True)
    args.page.write_text(render(receipt), encoding="utf-8")
    print(f"c_ub_audit: {receipt['status']} {receipt['completed']}/{receipt['total']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
