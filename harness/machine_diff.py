#!/usr/bin/env python3
"""Differential smoke rows for the AST small-step machine.

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

REPO_ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
TRACEBACK_CLASS = re.compile(r"(?:^|\s)([A-Za-z_][A-Za-z0-9_]*(?:Error|Interrupt|Exit|Exception|Warning))(?::|$)")


def oracle_result(oracle, source):
    proc = subprocess.run(
        [oracle, os.path.abspath(source)], cwd=REPO_ROOT,
        capture_output=True, text=True,
    )
    stdout = proc.stdout.splitlines()
    if proc.returncode == 0:
        return {"status": "ok", "exit": 0, "stdout": stdout}
    error = None
    for line in reversed(proc.stderr.splitlines()):
        match = TRACEBACK_CLASS.search(line.strip())
        if match:
            error = match.group(1)
            break
    return {"status": "exn", "exit": proc.returncode,
            "exn": error, "stdout": stdout}


def run_machine(runner, rows, fuel):
    fd, jobs_path = tempfile.mkstemp(prefix=".machine-jobs-", suffix=".jsonl")
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as jobs:
            for row in rows:
                jobs.write(json.dumps({"path": row["envelope"]}) + "\n")
        command = list(runner) + ["--machine-script-batch", jobs_path]
        if fuel is not None:
            command += ["--fuel", str(fuel)]
        proc = subprocess.run(command, cwd=REPO_ROOT,
                              capture_output=True, text=True)
        results = []
        for line in proc.stdout.splitlines():
            if line.startswith("{"):
                results.append(json.loads(line))
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
    oracle = []
    for row in rows:
        oracle.append(oracle_result(opts.oracle, row["source"]))
    machine, runner_code = run_machine(opts.runner.split(), rows, opts.fuel)

    matched = refused = divergent = 0
    for index, (row, expected, actual) in enumerate(zip(rows, oracle, machine), 1):
        if row["expect"] == "unsupported":
            verdict = "REFUSED" if actual.get("status") == "unsupported" else "DIVERGE"
            if verdict == "REFUSED":
                refused += 1
            else:
                divergent += 1
        else:
            same = (actual.get("status") == expected.get("status") and
                    actual.get("exit") == expected.get("exit") and
                    actual.get("stdout", []) == expected.get("stdout", []))
            verdict = "MATCH" if same else "DIVERGE"
            if same:
                matched += 1
            else:
                divergent += 1
        print("[%d/%d] %-8s %s" % (index, len(rows), verdict, row["source"]))
        if verdict == "DIVERGE":
            print("  cpython:", json.dumps(expected, sort_keys=True))
            print("  machine:", json.dumps(actual, sort_keys=True))

    comparable = sum(row["expect"] == "match" for row in rows)
    print("machine rows: %d, matched: %d, refused: %d, diverging: %d" %
          (len(rows), matched, refused, divergent))
    print("MACHINE-PARITY %d/%d, diverging %d" %
          (matched, comparable, divergent))
    if runner_code != 0 and divergent == 0:
        print("runner exit:", runner_code)
    return 1 if divergent else 0


if __name__ == "__main__":
    sys.exit(main())
