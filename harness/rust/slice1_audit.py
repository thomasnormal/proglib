#!/usr/bin/env python3
"""Run every Stage 0 corpus row through the Lean MIR semantics and compare with Miri.

Each row is extracted with the structured rustc_public extractor (this needs
the pinned nightly and its Miri sysroot; the corpus envelopes are not checked
in), loaded into Lean, and run with `runOutcome` in one Lean process.  The
Lean outcome is compared with the checked-in Stage 0 Miri verdicts: a return,
panic or UB that Miri does not report is `diverging`; a Lean refusal or an
exhausted fuel budget is a `named_refusal`.  The audit never parses Rust
source or a textual MIR dump.

LIMIT: every row of the current corpus exits 0 under Miri, so a wrong value
that still returns (or that only reaches a refused panic path) cannot show up
here.  Panic and UB rows are needed before `diverging: 0` means much.
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


# Lean outcome label -> the Miri verdict that agrees with it.  `refused:*` and
# `out_of_fuel` claim nothing and are never compared.
_LEAN_TO_MIRI = {"returned": "ok", "panicked": "panic"}


def _lean_class(label):
    if label in _LEAN_TO_MIRI:
        return _LEAN_TO_MIRI[label]
    if label.startswith("ub:"):
        return "ub"
    return None


def classify(lean_label, miri_verdicts):
    """Status and reason of one corpus row from its Lean outcome label and the
    set of Miri verdicts (one per borrow model).  Every outcome Lean decides
    (return, panic, UB) is compared with Miri, so a wrong panic or a wrong UB
    claim is a divergence, not a refusal."""
    lean = _lean_class(lean_label)
    if lean is None:
        return "named_refusal", "Lean outcome " + lean_label
    verdicts = ",".join(sorted(miri_verdicts))
    if len(miri_verdicts) != 1:
        return "named_refusal", "Miri borrow models disagree (" + verdicts + "); no claim"
    if miri_verdicts == {lean}:
        return "decided", "Lean " + lean_label + "; Miri Stage 0 verdict is " + verdicts
    return "diverging", "Lean " + lean_label + " but Miri verdict is " + verdicts


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest", default="harness/rust/measurement_manifest.json")
    parser.add_argument("--extractor")
    parser.add_argument("--work-root")
    parser.add_argument("--timeout", type=float, default=120.0)
    parser.add_argument("--output", required=True)
    parser.add_argument("--oracle", default="docs/rust-stage0-measurement.json",
                        help="checked-in Stage 0 Miri verdicts")
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
    oracle_rows = {
        row["id"]: row["oracle"]
        for row in json.loads(Path(args.oracle).read_text(encoding="utf-8"))["rows"]
    }
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
                rows.append({"id": item["id"], "source": item["path"],
                             "status": "pending", "reason": "Lean run pending",
                             "oracle": oracle_rows.get(item["id"], {}),
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
            lines.append(f"#eval LeanModels.Rust.Outcome.label (LeanModels.Rust.runOutcome {name})")
        main_file.write_text("\n".join(lines) + "\n", encoding="utf-8")
        command = ["lake", "env", "lean", str(main_file)]
        completed = subprocess.run(command, cwd=repo_root, text=True,
                                   stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                   check=False)
        values = []
        for line in completed.stdout.splitlines():
            line = line.strip()
            if line.startswith('"') and line.endswith('"'):
                values.append(json.loads(line))
        if completed.returncode != 0 or len(values) != len(names):
            raise RuntimeError("Lean corpus run failed:\n" + completed.stdout[-4000:] + completed.stderr[-4000:])
        for (item, _name), value in zip(names, values):
            row = next(row for row in rows if row["id"] == item["id"])
            oracle = oracle_rows[item["id"]]
            miri_verdicts = {model["verdict"] for model in oracle["models"].values()}
            row["lean_outcome"] = value
            row["status"], row["reason"] = classify(value, miri_verdicts)
    report = {
        "schema": "lean-surfaces.rust.slice1-audit.v0",
        "rows": rows,
        "decided_rows": sum(row["status"] == "decided" for row in rows),
        "named_refusals": sum(row["status"] in {"named_refusal", "extractor_refusal"} for row in rows),
        "diverging": sum(row["status"] == "diverging" for row in rows),
    }
    Path(args.output).write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"rows": len(rows), "decided": report["decided_rows"],
                      "named_refusals": report["named_refusals"],
                      "diverging": report["diverging"]}))


if __name__ == "__main__":
    main()
