#!/usr/bin/env python3
"""Differential smoke rows for the AST small-step relation.

The source files are executed by CPython, while the machine consumes the
already-generated CPython-AST envelopes.  The two inputs therefore share the
approved parser boundary without this harness parsing Python source text.
Rows marked ``unsupported`` are deliberate machine frontier checks.  They
must refuse loudly and are excluded from the parity denominator.
"""

import argparse
import json
import os
import re
import subprocess
import sys
import tempfile

if __name__ == "__main__" and sys.version_info[:2] != (3, 9):
    from shutil import which
    import os as _os
    _frontend = which("python3.9")
    if _frontend is not None and not _os.environ.get("MACHINE_DIFF_PINNED"):
        _os.environ["MACHINE_DIFF_PINNED"] = "1"
        _os.execv(_frontend, [_frontend, os.path.abspath(__file__)] + sys.argv[1:])

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TRACEBACK_CLASS = re.compile(r"(?:^|\s)([A-Za-z_][A-Za-z0-9_]*(?:Error|Interrupt|Exit|Exception|Warning))(?::|$)")
RELATION_CASE_TOTAL = 5033


def oracle_result(oracle, source):
    proc = subprocess.run(
        [oracle, os.path.abspath(source)], cwd=REPO_ROOT,
        capture_output=True, text=True,
    )
    stdout = proc.stdout.splitlines()
    if proc.returncode == 0:
        return {"status": "ok", "exit": 0, "stdout": stdout,
                "stdout_text": proc.stdout}
    error = None
    for line in reversed(proc.stderr.splitlines()):
        match = TRACEBACK_CLASS.search(line.strip())
        if match:
            error = match.group(1)
            break
    return {"status": "exn", "exit": proc.returncode,
            "exn": error, "stdout": stdout, "stdout_text": proc.stdout}


def refresh_envelopes(rows):
    """Re-extract every row through the shared pinned frontend/cache path."""
    import importlib.machinery
    import importlib.util
    path = os.path.join(REPO_ROOT, "tools", "leanpy")
    spec = importlib.util.spec_from_loader(
        "machine_diff_leanpy", importlib.machinery.SourceFileLoader("machine_diff_leanpy", path))
    leanpy = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(leanpy)
    cache = leanpy.default_cache()
    refreshed = []
    for row in rows:
        envelope = leanpy.envelope_for(row["source"], cache)
        if envelope is None:
            raise RuntimeError("extractor refused %s" % row["source"])
        current = dict(row)
        current["envelope"] = envelope
        refreshed.append(current)
    return refreshed


def run_relation(runner, rows, fuel):
    fd, jobs_path = tempfile.mkstemp(prefix=".machine-jobs-", suffix=".jsonl")
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as jobs:
            for row in rows:
                jobs.write(json.dumps({"path": row["envelope"]}) + "\n")
        command = list(runner) + ["--relation-script-batch", jobs_path]
        if fuel is not None:
            command += ["--fuel", str(fuel)]
        proc = subprocess.run(command, cwd=REPO_ROOT,
                              capture_output=True, text=True)
        results = []
        for line in proc.stdout.splitlines():
            if line.startswith("{"):
                result = json.loads(line)
                chunks = result.get("stdout", [])
                result["stdout_text"] = "".join(chunk + "\n" for chunk in chunks)
                results.append(result)
        while len(results) < len(rows):
            results.append({"status": "runner-error", "exit": 1})
        return results, proc.returncode
    finally:
        os.unlink(jobs_path)


def main(argv=None):
    parser = argparse.ArgumentParser(prog="machine_diff.py")
    parser.add_argument("--cases", default="harness/machine_cases.json")
    parser.add_argument("--oracle", default="python3.9")
    parser.add_argument("--runner", default="lake exe leanmodels-run")
    parser.add_argument("--fuel", type=int, default=4096)
    opts = parser.parse_args(argv)
    os.chdir(REPO_ROOT)

    with open(opts.cases, encoding="utf-8") as stream:
        rows = json.load(stream)
    rows = refresh_envelopes(rows)
    oracle = []
    for row in rows:
        oracle.append(oracle_result(opts.oracle, row["source"]))
    machine, runner_code = run_relation(opts.runner.split(), rows, opts.fuel)

    matched = refused = divergent = 0
    unit_mismatches = 0
    for index, (row, expected, actual) in enumerate(zip(rows, oracle, machine), 1):
        unit_expected_refusal = row["expect"] == "unsupported"
        if (actual.get("status") == "unsupported") != unit_expected_refusal:
            unit_mismatches += 1
        if actual.get("status") == "unsupported":
            verdict = "REFUSED"
            refused += 1
        else:
            same = (actual.get("status") == expected.get("status") and
                    actual.get("exit") == expected.get("exit") and
                    actual.get("stdout_text", "") == expected.get("stdout_text", "") and
                    actual.get("exn") == expected.get("exn"))
            verdict = "MATCH" if same else "DIVERGE"
            if same:
                matched += 1
            else:
                divergent += 1
        print("[%d/%d] %-8s %s" % (index, len(rows), verdict, row["source"]))
        if verdict == "DIVERGE":
            print("  cpython:", json.dumps(expected, sort_keys=True))
            print("  machine:", json.dumps(actual, sort_keys=True))

    comparable = matched + divergent
    print("machine rows: %d, matched: %d, refused: %d, diverging: %d" %
          (len(rows), matched, refused, divergent))
    print("MACHINE-PARITY %d/%d, diverging %d" %
          (matched, comparable, divergent))
    print("MACHINE-UNIT rows %d, expectation mismatches %d" %
          (len(rows), unit_mismatches))
    if runner_code != 0 and divergent == 0:
        print("runner exit:", runner_code)
    version = subprocess.run([opts.oracle, "-V"], capture_output=True, text=True)
    print("oracle: %s" % ((version.stdout or version.stderr).strip(),))
    # The relation currently has a module-script adapter only.  Keep the
    # project's full typed-call denominator visible until that adapter lands,
    # and never infer decisions from the legacy runner's expectations.
    relation_case_decided = 0
    relation_case_divergent = 0
    print("MACHINE-REL cases %d/%d (diverge %d)" %
          (relation_case_decided, RELATION_CASE_TOTAL, relation_case_divergent))
    return 1 if (divergent or unit_mismatches or runner_code != 0 or
                 relation_case_divergent) else 0


if __name__ == "__main__":
    sys.exit(main())
