#!/usr/bin/env python3
"""Offline checks for an F2 native-placement replay fixture."""

import argparse
import hashlib
import json
import subprocess
import tempfile
from pathlib import Path

PIN = "clang version 21.1.8"


def check(fixture, source=None):
    required = ("source_hash", "compiler_version", "target_triple",
                "placements", "events", "ending")
    missing = [key for key in required if key not in fixture]
    if missing:
        return "missing fields: " + ", ".join(missing)
    if source is not None:
        digest = hashlib.sha256(Path(source).read_bytes()).hexdigest()
        if digest != fixture["source_hash"]:
            return "source hash mismatch"
    if not fixture["compiler_version"].startswith(PIN):
        return "compiler pin mismatch"
    placements = fixture["placements"]
    intervals = sorted((p["base"], p["base"] + p["size"]) for p in placements)
    if any(right > left_end for (_, left_end), (right, _) in zip(intervals, intervals[1:])):
        return "placements overlap"
    if not isinstance(fixture["events"], list):
        return "events must be a list"
    ending = fixture["ending"]
    if ending.get("kind") == "ub" and not ending.get("clause_operand"):
        return "UB ending lacks cited clause and operand"
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("fixture", type=Path, nargs="?")
    parser.add_argument("--source", type=Path)
    parser.add_argument("--native", action="store_true")
    parser.add_argument("--sanitizer", action="store_true")
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        good = {"source_hash": "x", "compiler_version": PIN,
                "target_triple": "x86_64", "placements": [],
                "events": [], "ending": {"kind": "exit", "status": 0}}
        bad = dict(good, compiler_version="clang version 20")
        assert check(good) is None
        assert check(bad) == "compiler pin mismatch"
        print("f2_replay_check --self-test: ok")
        return 0
    if args.fixture is None:
        parser.error("fixture is required unless --self-test is used")
    fixture = json.loads(args.fixture.read_text())
    fixtures = fixture if isinstance(fixture, list) else [fixture]
    for item in fixtures:
        error = check(item, args.source)
        if error:
            raise SystemExit("f2_replay_check: " + error)
        if args.native:
            source = args.source or Path(item.get("source_file", ""))
            with tempfile.TemporaryDirectory(prefix="f2-replay-") as tmp:
                outcomes = []
                for opt in ("-O0", "-O2"):
                    binary = Path(tmp) / opt[1:]
                    build = subprocess.run(["clang", "-std=gnu17", opt,
                                            str(source), "-o", str(binary)],
                                           capture_output=True, text=True)
                    if build.returncode:
                        raise SystemExit("f2_replay_check: native compile failed")
                    run = subprocess.run([str(binary)], capture_output=True)
                    outcomes.append((run.returncode, run.stdout))
                if outcomes[0] != outcomes[1]:
                    raise SystemExit("f2_replay_check: O0/O2 outcome mismatch")
                ending = item["ending"]
                if ending.get("kind") == "exit" and outcomes[0][0] != ending["status"]:
                    raise SystemExit("f2_replay_check: exit status mismatch")
                if args.sanitizer:
                    binary = Path(tmp) / "sanitized"
                    build = subprocess.run(
                        ["clang", "-std=gnu17", "-O0", "-fsanitize=undefined,address",
                         "-fno-sanitize-recover=all", str(source), "-o", str(binary)],
                        capture_output=True, text=True)
                    if build.returncode:
                        raise SystemExit("f2_replay_check: sanitizer compile failed")
                    run = subprocess.run([str(binary)], capture_output=True, text=True)
                    if run.returncode != ending.get("status", run.returncode) or run.stderr:
                        raise SystemExit("f2_replay_check: sanitizer evidence mismatch")
    print("f2_replay_check: ok")


if __name__ == "__main__":
    main()
