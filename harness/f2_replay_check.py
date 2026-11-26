#!/usr/bin/env python3
"""Offline checks for an F2 native-placement replay fixture."""

import argparse
import hashlib
import json
import os
import re
import shutil
import subprocess
import tempfile
from pathlib import Path

PIN = "clang version 21.1.8"


def pinned_clang():
    requested = os.environ.get("LEAN_C_CLANG", "clang")
    executable = (requested if os.path.basename(requested) != requested
                  else shutil.which(requested))
    if not executable or not os.path.exists(executable):
        raise SystemExit("f2_replay_check: pinned Clang executable is unavailable")
    version = subprocess.run([executable, "--version"], capture_output=True,
                             text=True)
    first = version.stdout.splitlines()[0] if version.stdout else ""
    if version.returncode != 0 or not first.startswith(PIN):
        raise SystemExit("f2_replay_check: expected %s, got %s" %
                         (PIN, first or "<none>"))
    return executable


def expected_stdout(events):
    return "".join(event.get("data", "") for event in events
                    if event.get("kind") == "io" and
                    event.get("channel") == "stdout").encode()


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
    if not re.fullmatch(r"[0-9a-f]{64}", fixture["source_hash"]):
        return "source hash is not a SHA-256 digest"
    if not fixture["compiler_version"].startswith(PIN):
        return "compiler pin mismatch"
    placements = fixture["placements"]
    intervals = sorted((p["base"], p["base"] + p["size"]) for p in placements)
    if any(right < left_end for (_, left_end), (right, _) in zip(intervals, intervals[1:])):
        return "placements overlap"
    if not isinstance(fixture["events"], list):
        return "events must be a list"
    forbidden = {"address", "allocation", "base", "pointer_id"}
    for event in fixture["events"]:
        if not isinstance(event, dict):
            return "events must contain objects"
        if forbidden.intersection(event):
            return "observable event exposes placement identity"
        kind = event.get("kind")
        if kind == "io":
            if (not isinstance(event.get("operation"), str) or
                    not isinstance(event.get("channel"), str) or
                    not isinstance(event.get("data"), str)):
                return "io event has malformed fields"
        elif kind in {"volatileRead", "volatileWrite"}:
            data = event.get("data")
            if (not isinstance(data, list) or
                    any(not isinstance(byte, int) or not 0 <= byte <= 255
                        for byte in data)):
                return "volatile event has malformed bytes"
        else:
            return "unknown event kind"
    for placement in placements:
        if not isinstance(placement.get("exposed"), bool):
            return "placement exposure flag is not boolean"
    ending = fixture["ending"]
    kind = ending.get("kind")
    if kind not in {"exit", "signal", "exhausted", "diverges", "ub", "refused"}:
        return "unknown ending kind"
    if kind == "ub":
        evidence = ending.get("clause_operand", {})
        if (not isinstance(evidence, dict) or
                not evidence.get("clause") or not evidence.get("operand")):
            return "UB ending lacks cited clause and operand"
    if kind == "exhausted" and ending.get("prefix_complete") is not True:
        return "exhaustion ending lacks complete observable prefix"
    removal = fixture.get("allocation_removal")
    if removal is not None:
        if removal.get("null_folded") is True and removal.get("free_null") is not True:
            return "removed allocation null branch lacks free(NULL) step"
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
        good = {"source_hash": "0" * 64, "compiler_version": PIN,
                "target_triple": "x86_64", "placements": [],
                "events": [], "ending": {"kind": "exit", "status": 0}}
        bad = dict(good, compiler_version="clang version 20")
        placeholder = dict(good, source_hash="placeholder")
        leaking = dict(good, events=[{"kind": "io", "address": 4}])
        bad_ub = dict(good, ending={"kind": "ub", "clause_operand": {"clause": "6.5"}})
        bad_exhaustion = dict(good, ending={"kind": "exhausted"})
        bad_removal = dict(good, allocation_removal={"null_folded": True, "free_null": False})
        bad_event = dict(good, events=[{"kind": "io", "channel": "stdout"}])
        bad_event_kind = dict(good, events=[{"kind": "clock", "data": "x"}])
        bad_volatile = dict(good, events=[{"kind": "volatileRead", "data": [256]}])
        first = {"allocation": 1, "base": 16, "size": 8, "exposed": False}
        second = {"allocation": 2, "base": 32, "size": 8, "exposed": True}
        separated = dict(good, placements=[second, first])
        adjacent = dict(good, placements=[first, dict(second, base=24)])
        overlapping = dict(good, placements=[first, dict(second, base=23)])
        enclosing = dict(good, placements=[first, dict(second, base=18, size=2)])
        assert check(good) is None
        assert check(bad) == "compiler pin mismatch"
        assert check(placeholder) == "source hash is not a SHA-256 digest"
        assert check(leaking) == "observable event exposes placement identity"
        assert check(bad_ub) == "UB ending lacks cited clause and operand"
        assert check(bad_exhaustion) == "exhaustion ending lacks complete observable prefix"
        assert check(bad_removal) == "removed allocation null branch lacks free(NULL) step"
        assert check(bad_event) == "io event has malformed fields"
        assert check(bad_event_kind) == "unknown event kind"
        assert check(bad_volatile) == "volatile event has malformed bytes"
        assert check(separated) is None
        assert check(adjacent) is None
        assert check(overlapping) == "placements overlap"
        assert check(enclosing) == "placements overlap"
        print("f2_replay_check --self-test: ok")
        return 0
    if args.fixture is None:
        parser.error("fixture is required unless --self-test is used")
    fixture = json.loads(args.fixture.read_text())
    fixtures = fixture if isinstance(fixture, list) else [fixture]
    clang = pinned_clang() if args.native else None
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
                    build = subprocess.run([clang, "-std=gnu17", opt,
                                            str(source), "-o", str(binary)],
                                           capture_output=True, text=True)
                    if build.returncode:
                        raise SystemExit("f2_replay_check: native compile failed")
                    run = subprocess.run([str(binary)], capture_output=True)
                    outcomes.append((run.returncode, run.stdout))
                if outcomes[0] != outcomes[1]:
                    raise SystemExit("f2_replay_check: O0/O2 outcome mismatch")
                if run.stdout != expected_stdout(item["events"]):
                    raise SystemExit("f2_replay_check: stdout event mismatch")
                ending = item["ending"]
                if ending.get("kind") == "exit" and outcomes[0][0] != ending["status"]:
                    raise SystemExit("f2_replay_check: exit status mismatch")
                if args.sanitizer:
                    binary = Path(tmp) / "sanitized"
                    build = subprocess.run(
                        [clang, "-std=gnu17", "-O0", "-fsanitize=undefined,address",
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
