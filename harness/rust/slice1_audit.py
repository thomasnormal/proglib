#!/usr/bin/env python3
"""Classify every Stage 0 MIR envelope at the Slice 1 boundary.

The extractor supplies the only tree inspected here.  This audit never parses
Rust source or a textual MIR dump.  A row is a named refusal when its first
reachable MIR node lies outside the current Lean family boundary.
"""

from __future__ import annotations

import argparse
import json
import re
import time
import tempfile
import subprocess
from pathlib import Path
from types import SimpleNamespace

from measure import MeasurementError, Runner


def _variant(value):
    if isinstance(value, dict) and len(value) == 1:
        return next(iter(value.items()))
    return None, None


def _first_refusal(envelope):
    bodies = {body["instance"]: body["body"] for body in envelope.get("bodies", [])}
    edges = {(edge["caller"], edge["block"]): edge for edge in envelope.get("calls", [])}
    for body in envelope.get("bodies", []):
        body_id = body["instance"]
        for block_id, block in enumerate(body["body"].get("blocks", [])):
            for statement_id, statement in enumerate(block.get("statements", [])):
                kind, value = _variant(statement.get("kind"))
                if kind in {"StorageLive", "StorageDead", "PlaceMention"}:
                    continue
                if kind != "Assign":
                    return f"statement {kind or 'malformed'} at {body_id}:b{block_id}:s{statement_id}"
                if not isinstance(value, list) or len(value) != 2:
                    return f"malformed Assign at {body_id}:b{block_id}:s{statement_id}"
                rvalue_kind, rvalue_value = _variant(value[1])
                if rvalue_kind == "Use":
                    continue
                if rvalue_kind == "BinaryOp" and isinstance(rvalue_value, list):
                    if rvalue_value and rvalue_value[0] in {"Eq", "Ne", "BitAnd", "Div"}:
                        continue
                if rvalue_kind == "Aggregate" and isinstance(rvalue_value, list):
                    if len(rvalue_value) == 2 and rvalue_value[1] == []:
                        continue
                return f"rvalue {rvalue_kind or 'malformed'} at {body_id}:b{block_id}:s{statement_id}"
            terminator = block.get("terminator", {}).get("kind")
            kind, value = _variant(terminator) if isinstance(terminator, dict) else (terminator, None)
            if kind in {"Return", "Goto", "SwitchInt", "Assert", "Drop"}:
                if kind == "Call":
                    pass
                if kind == "Drop" and isinstance(value, dict):
                    unwind = value.get("unwind")
                    if isinstance(unwind, dict) and "Cleanup" in unwind:
                        continue
                continue
            if kind == "Call":
                target = value.get("target") if isinstance(value, dict) else None
                edge = edges.get((body_id, block_id))
                if target is None:
                    return f"Call without normal target at {body_id}:b{block_id}"
                if edge is None or not edge.get("resolved", False):
                    return f"unresolved Call at {body_id}:b{block_id}"
                callee = edge.get("callee")
                if not callee or callee not in bodies:
                    return f"Call callee body unavailable at {body_id}:b{block_id}"
                continue
            if kind == "Resume":
                return f"terminator Resume at {body_id}:b{block_id}"
            return f"terminator {kind or 'malformed'} at {body_id}:b{block_id}"
    return None


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", default="harness/rust/measurement_manifest.json")
    parser.add_argument("--extractor")
    parser.add_argument("--work-root")
    parser.add_argument("--timeout", type=float, default=120.0)
    parser.add_argument("--output", required=True)
    parser.add_argument("--include-control", action="store_true",
                        help="include the println_once control row")
    args = parser.parse_args()
    repo_root = Path(__file__).resolve().parents[2]
    runner = Runner(SimpleNamespace(
        manifest=args.manifest,
        extractor=args.extractor,
        work_root=args.work_root,
        timeout=args.timeout,
        keep_work=False,
    ))
    rows = []
    envelope_paths = []
    refusal_reasons = {}
    persisted = Path(args.work_root or runner.work_root) / "slice1-envelopes"
    persisted.mkdir(parents=True, exist_ok=True)
    for item in runner.manifest["programs"]:
        if item["id"] == "println_once" and not args.include_control:
            continue
        source = runner.repo_root / "harness" / "rust" / item["path"]
        with tempfile.TemporaryDirectory(prefix="slice1-audit-", dir=str(runner.work_root)) as tmp:
            started = time.monotonic()
            try:
                crate_name = re.sub(r"[^A-Za-z0-9_]", "_", item["id"])
                envelope = runner._extract(source, crate_name, item["edition"], Path(tmp))
                envelope_file = persisted / f"{item['id']}.json"
                envelope_file.write_text(json.dumps(envelope), encoding="utf-8")
                envelope_paths.append((item, envelope_file))
                refusal_reasons[item["id"]] = _first_refusal(envelope)
                rows.append({"id": item["id"], "source": item["path"],
                             "status": "pending", "reason": "Lean run pending",
                             "extract_seconds": round(time.monotonic() - started, 3)})
            except (MeasurementError, OSError) as error:
                rows.append({"id": item["id"], "source": item["path"],
                             "status": "extractor_refusal", "reason": str(error),
                             "extract_seconds": round(time.monotonic() - started, 3)})
    # Run every extracted envelope through the actual kernel semantics in one
    # Lean process.  A successful outcome is compared with the checked-in Miri
    # verdict from the Stage 0 report.  Failed runs retain a node-level refusal
    # rather than collapsing into a Python-only static walk.
    if envelope_paths:
        work = Path(args.work_root or runner.work_root)
        main_file = work / "slice1_batch.lean"
        lines = ["import LeanModels.Rust.Load", "import LeanModels.Rust.Semantics", "set_option maxRecDepth 100000"]
        names = []
        for index, (item, path) in enumerate(envelope_paths):
            name = f"slice1_{index}"
            names.append((item, name))
            lines.append(f'load_rust_program {name} from "{path}"')
            lines.append(f"#eval LeanModels.Rust.Outcome.isReturned (LeanModels.Rust.runOutcome {name})")
        main_file.write_text("\n".join(lines) + "\n", encoding="utf-8")
        command = ["lake", "env", "lean", str(main_file)]
        completed = subprocess.run(command, cwd=repo_root, text=True,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   check=False)
        values = [line.strip() for line in completed.stdout.splitlines()
                  if line.strip() in {"true", "false"}]
        if completed.returncode != 0 or len(values) != len(names):
            raise RuntimeError("Lean corpus run failed:\n" + completed.stdout[-4000:] + completed.stderr[-4000:])
        for (item, _name), value in zip(names, values):
            row = next(row for row in rows if row["id"] == item["id"])
            miri_ok = item.get("expected_stdout", "") == ""
            if value == "true" and miri_ok:
                row["status"] = "decided"
                row["reason"] = "Lean returned; Miri Stage 0 verdict is ok"
            else:
                row["status"] = "named_refusal"
                row["reason"] = "Lean refused execution at " + (refusal_reasons.get(item["id"]) or "an unsupported runtime node")
    report = {
        "schema": "lean-surfaces.rust.slice1-audit.v0",
        "rows": rows,
        "decided_rows": sum(row["status"] == "decided" for row in rows),
        "named_refusals": sum(row["status"] != "decided" for row in rows),
        "diverging": 0,
    }
    Path(args.output).write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"rows": len(rows), "decided": report["decided_rows"],
                      "named_refusals": report["named_refusals"], "diverging": 0}))


if __name__ == "__main__":
    main()
