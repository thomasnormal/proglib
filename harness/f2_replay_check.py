#!/usr/bin/env python3
"""Offline checks for an F2 native-placement replay fixture."""

import argparse
import hashlib
import json
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
    print("f2_replay_check: ok")


if __name__ == "__main__":
    main()
