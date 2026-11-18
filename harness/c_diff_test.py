#!/usr/bin/env python3
"""Pinned Clang/Lean differential rows for the C tier.

Every row compiles the unchanged source with the exact pinned compiler and
profile flags, extracts the same source with that compiler, and runs the
resulting envelope through the C model. Missing or mismatched oracle inputs are
ORACLE, never a green match.  A native assertion/UB result is a refusal or
divergence according to the row, never an unavailable oracle.
"""

from __future__ import print_function

import argparse
import importlib.util
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
CASES = ROOT / "harness" / "c_cases.json"
_extract_spec = importlib.util.spec_from_file_location(
    "c_extractor_pin", ROOT / "extractors" / "c" / "extract.py")
_extract = importlib.util.module_from_spec(_extract_spec)
_extract_spec.loader.exec_module(_extract)
PINNED_VERSION = _extract.PINNED_FRONTEND_VERSION
PROFILE_FLAGS = ["-std=c23", "-D_FORTIFY_SOURCE=0"]
COMPILE_FLAGS = ["--no-default-config", "-std=c23", "-O0", "-g",
                 "-D_FORTIFY_SOURCE=0", "-fno-strict-aliasing"]


def run(args, env=None, timeout=120):
    return subprocess.run(args, cwd=str(ROOT), env=env, text=True,
                          capture_output=True, timeout=timeout)


def oracle():
    requested = os.environ.get("LEAN_C_CLANG", "clang")
    executable = shutil.which(requested) if os.path.basename(requested) == requested else requested
    if not executable or not os.path.exists(executable):
        return None, "set LEAN_C_CLANG to the pinned compiler"
    probed = run([executable, "--version"])
    first = probed.stdout.splitlines()[0] if probed.stdout else ""
    if probed.returncode != 0 or first != PINNED_VERSION:
        return None, "expected %s, got %s" % (PINNED_VERSION, first or "<none>")
    return executable, first


def model_env(clang, record_layout_plugin=None, structured_type_plugin=None):
    env = dict(os.environ)
    env["LEAN_C_CLANG"] = clang
    if record_layout_plugin:
        env["LEAN_C_RECORD_LAYOUT_PLUGIN"] = record_layout_plugin
    if structured_type_plugin:
        env["LEAN_C_STRUCTURED_TYPE_PLUGIN"] = structured_type_plugin
    return env


def walk(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def check_envelope(payload, checks, name):
    nodes = list(walk(payload))
    for check in checks:
        if check == "array_filler":
            if not any(n.get("kind") == "InitListExpr" and
                       "array_filler" in n for n in nodes):
                return name + ": missing required array_filler field"
        elif check == "compound_promotion":
            compounds = [n for n in nodes
                         if n.get("kind") == "CompoundAssignOperator"]
            if not compounds or any(not n.get("compute_lhs_type") or
                                    not n.get("compute_result_type")
                                    for n in compounds):
                return name + ": missing Clang compound promotion evidence"
        elif check == "record_attributes":
            wanted = {"P": "MaxFieldAlignmentAttr", "Q": "PackedAttr",
                      "R": "AlignedAttr"}
            records = {n.get("name"): n for n in nodes
                       if n.get("kind") == "RecordDecl"}
            for record, attr in wanted.items():
                fields = records.get(record, {}).get("fields", [])
                found = {f.get("c_kind") for f in fields
                         if f.get("kind") == "Unsupported"}
                if attr not in found:
                    return name + ": attribute was dropped: " + record
        elif check == "record_layout":
            if not any(n.get("kind") == "RecordDecl" and
                       isinstance(n.get("record_layout"), dict)
                       for n in nodes):
                return name + ": missing parser-native record layout"
        elif check == "type_layout":
            if not payload.get("type_layouts"):
                return name + ": missing parser-native type layout"
        elif check == "type_layout_sizes":
            layouts = payload.get("type_layouts")
            if not isinstance(layouts, list) or not any(
                    row.get("element_size_bytes") == 4 for row in layouts):
                return name + ": missing parser-native array element size"
            if not any(row.get("pointee_size_bytes") == 4 for row in layouts):
                return name + ": missing parser-native pointer pointee size"
        elif check == "structured_types":
            rows = payload.get("structured_types")
            if not isinstance(rows, list) or not rows:
                return name + ": missing parser-native structured types"
            if any(not isinstance(row, dict) or
                   not isinstance(row.get("decl_id"), str) or
                   not isinstance(row.get("type"), dict) for row in rows):
                return name + ": malformed parser-native structured type"
        else:
            return name + ": unknown envelope check " + check
    return None


def selected(row, key, record_layout_plugin):
    """Use the layout-backed expectation only for a layout-backed run."""
    if record_layout_plugin:
        return row.get("layout_" + key, row.get(key))
    return row.get(key)


def classify(row, clang, work, record_layout_plugin=None, structured_type_plugin=None):
    source = work / (row["id"] + ".c")
    source.write_text(row["source"] + "\n", encoding="utf-8")
    native = work / row["id"]
    flags = list(COMPILE_FLAGS)
    if row.get("sanitize"):
        flags += ["-fsanitize=undefined", "-fno-sanitize-recover=all"]
    compiled = run([clang] + flags + [str(source), "-o", str(native)])
    if compiled.returncode:
        return "ORACLE", "native compile failed: " + compiled.stderr[-800:]
    native_run = run([str(native)], timeout=30)

    envelope = work / (row["id"] + ".json")
    extracted = run([sys.executable, "extractors/c/extract.py", str(source),
                     "-o", str(envelope)],
                     env=model_env(clang, record_layout_plugin, structured_type_plugin))
    if extracted.returncode:
        return "EXTRACT", extracted.stderr[-800:]
    payload = json.loads(envelope.read_text(encoding="utf-8"))
    checks = list(row.get("envelope_checks", []))
    if record_layout_plugin:
        checks += row.get("layout_envelope_checks", [])
    if structured_type_plugin:
        checks += row.get("structured_envelope_checks", [])
    problem = check_envelope(payload, checks, row["id"])
    if problem:
        return "EXTRACT", problem
    version = payload.get("frontend", {}).get("version")
    if version != PINNED_VERSION:
        return "EXTRACT", "envelope frontend.version is not pinned: %r" % version

    runner = ROOT / ".lake" / "build" / "bin" / "c-torture-run"
    command = [str(runner)] if runner.exists() else ["lake", "exe", "c-torture-run"]
    model = run(command + ["--single", str(envelope), "512"],
                env=model_env(clang, record_layout_plugin, structured_type_plugin), timeout=180)
    expected_kind = selected(row, "expect", record_layout_plugin)
    if expected_kind == "refuse":
        if model.returncode == 3:
            detail = model.stderr.strip() or "native exit %d" % native_run.returncode
            expected_error = selected(row, "error", record_layout_plugin)
            if expected_error and expected_error not in detail:
                return "DIVERGE", "expected refusal %r, got %r" % (expected_error, detail)
            return "REFUSE", detail
        if model.returncode == 0:
            return "DIVERGE", "model returned %s for a refusal row" % model.stdout.strip()
        return "ORACLE", "model runner failed: " + (model.stderr or model.stdout)[-800:]

    if model.returncode != 0:
        return "DIVERGE", "model refused: " + (model.stderr or model.stdout)[-800:]
    try:
        marker = model.stdout.rfind("ok\t")
        line = model.stdout[marker:].splitlines()[0] if marker >= 0 else ""
        value = int(line.split("\t", 1)[1])
    except (ValueError, IndexError):
        return "DIVERGE", "model did not print an integer: %r" % model.stdout
    expected = int(selected(row, "return_value", record_layout_plugin))
    native_value = native_run.returncode if native_run.returncode >= 0 else None
    if value != expected or native_value != (expected % 256):
        return "DIVERGE", "model=%d native_exit=%r expected=%d" % (value, native_value, expected)
    if "expected_stdout" in row:
        marker = model.stdout.rfind("ok\t")
        model_stdout = model.stdout[:marker] if marker >= 0 else ""
        expected_stdout = row["expected_stdout"]
        if model_stdout != expected_stdout or native_run.stdout != expected_stdout:
            return "DIVERGE", "stdout model=%r native=%r expected=%r" % (
                model_stdout, native_run.stdout, expected_stdout)
    return "MATCH", "model=%d native_exit=%d" % (value, native_value)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--allow-oracle", action="store_true",
                    help="report exploratory ORACLE rows without failing")
    ap.add_argument("--id", action="append", dest="ids",
                    help="run only the named case (repeat for several cases)")
    ap.add_argument("--json", type=Path)
    ap.add_argument("--record-layout-plugin", default=os.environ.get(
        "LEAN_C_RECORD_LAYOUT_PLUGIN"),
        help="Clang plugin for parser-native record and object layouts")
    ap.add_argument("--structured-type-plugin", default=os.environ.get(
        "LEAN_C_STRUCTURED_TYPE_PLUGIN"),
        help="Clang plugin for parser-native recursive QualType observations")
    args = ap.parse_args()
    rows = json.loads(CASES.read_text(encoding="utf-8"))
    if args.ids:
        wanted = set(args.ids)
        rows = [row for row in rows if row["id"] in wanted]
        missing = wanted - {row["id"] for row in rows}
        if missing:
            ap.error("unknown case id(s): " + ", ".join(sorted(missing)))
    clang, detail = oracle()
    print("C oracle:", detail)
    if clang is None:
        counts = {"ORACLE": len(rows)}
        for row in rows:
            print(row["id"] + ": ORACLE " + detail)
        if args.json:
            args.json.write_text(json.dumps({"compiler": detail, "counts": counts}, indent=2) + "\n")
        return 0 if args.allow_oracle else 2
    counts = {}
    results = {}
    with tempfile.TemporaryDirectory(prefix="c-diff-") as temp:
        work = Path(temp)
        for row in rows:
            verdict, why = classify(row, clang, work, args.record_layout_plugin,
                                    args.structured_type_plugin)
            counts[verdict] = counts.get(verdict, 0) + 1
            results[row["id"]] = {"verdict": verdict, "detail": why}
            print(row["id"] + ": " + verdict + " " + why)
    if args.json:
        args.json.write_text(json.dumps({"compiler": detail, "counts": counts,
                                         "rows": results}, indent=2, sort_keys=True) + "\n")
    if counts.get("DIVERGE") or counts.get("EXTRACT") or counts.get("TIMEOUT"):
        return 1
    if counts.get("ORACLE") and not args.allow_oracle:
        return 2
    return 0


if __name__ == "__main__":
    sys.exit(main())
