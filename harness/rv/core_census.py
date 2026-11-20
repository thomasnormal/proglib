#!/usr/bin/env python3
"""Report the constructs emitted by canonical E's SystemVerilog loader.

This instrument deliberately does not reimplement admission rules.  A
generated Lean probe runs ``load_design_sv2`` and ``instantiateCoreMem`` on
the envelope.  Rows are taken from the resulting ``CoreMemDesign``.  A design
that the loader refuses produces one refusal row, preserving the exact
loader message.  The loaded instance has no source-level inactive branches,
so this census reports ``NOT REACHED=0`` and does not invent reachability
statuses from envelope syntax.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
from typing import Any


SCHEMA = "sv-core-census/loader-1"
STATUSES = ("ADMITTED", "REFUSED", "NOT REACHED")
ROOT = Path(__file__).resolve().parents[2]


def _envelope(path: Path) -> tuple[str, list[int]]:
    data = json.loads(path.read_text())
    if data.get("schema_version") != "sv-0.2":
        raise ValueError("envelope must be an sv-0.2 document")
    modules = data.get("design", {}).get("modules", [])
    if not modules or not isinstance(modules[0], dict):
        raise ValueError("envelope design.modules must contain the top module")
    params = modules[0].get("params", [])
    args: list[int] = []
    for param in params:
        if param.get("kind") != "ParameterDecl":
            continue
        value = param.get("resolved")
        if not isinstance(value, int):
            raise ValueError("loader census needs resolved parameter metadata")
        args.append(value)
    top = data.get("top")
    if not isinstance(top, str):
        raise ValueError("envelope top must be a string")
    return top, args


def _probe(path: Path, args: list[int]) -> str:
    resolved = path.resolve()
    try:
        source_path = resolved.relative_to(ROOT).as_posix()
    except ValueError:
        # Pinned third-party envelopes are often kept in the lane scratch
        # area.  The loader accepts an absolute path, and the census must not
        # require copying a generated envelope into the repository.
        source_path = resolved.as_posix()
    literal_args = " ".join(str(value) for value in args)
    source = f'''import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 core from "{source_path}"
def procKind : CoreMemProc → String
  | .edge _ => "edge"
  | .assign _ _ => "assign"
  | .primitive op _ _ => "primitive:" ++ op
  | .initial _ => "initial"
  | .comb _ => "always_comb"
  | .implicit _ => "always @*"
  | .event events _ => "always event (" ++ toString events.length ++ ")"
  | .latch _ => "always_latch"
  | .unsupported kind text => "REFUSED " ++ kind ++ " " ++ text
def procRows : Nat → List CoreMemProc → List String
  | _, [] => []
  | i, p :: rest => ("PROC " ++ toString i ++ " " ++ procKind p) :: procRows (i + 1) rest
def rows (d : CoreMemDesign) : String :=
  let memories := d.memories.toList.map (fun m => "MEM " ++ m.source.name)
  let decls := d.scalar.decls.toList.map (fun decl => "DECL " ++ decl.name)
  let processes := procRows 0 d.processes.toList
  String.intercalate "\\n" (memories ++ decls ++ processes)
#eval match core.e {literal_args} with
  | .ok d => "OK\\n" ++ rows d
  | .timeout => "TIMEOUT"
  | .unsupported message => "REFUSED\\n" ++ message
'''
    tmpdir = Path(os.environ.get("TMPDIR", str(ROOT / ".lake" / "tmp")))
    tmpdir.mkdir(parents=True, exist_ok=True)
    probe = ROOT / ".lake" / f"core-census-{os.getpid()}.lean"
    probe.write_text(source)
    try:
        result = subprocess.run(
            ["lake", "env", "lean", str(probe)],
            cwd=ROOT,
            env={**os.environ, "TMPDIR": str(tmpdir)},
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
            timeout=900,
        )
    finally:
        probe.unlink(missing_ok=True)
    if result.returncode:
        refused = " REFUSED — "
        lines = result.stdout.splitlines()
        for index, line in enumerate(lines):
            marker_index = line.find(refused)
            if marker_index < 0:
                continue
            message_lines = [line[marker_index + len(refused):]]
            for continuation in lines[index + 1:]:
                if "error(" in continuation:
                    break
                message_lines.append(continuation)
            return "REFUSED\n" + "\n".join(message_lines).strip()
        raise RuntimeError(result.stdout)
    for line in reversed(result.stdout.splitlines()):
        if line.startswith('"') and line.endswith('"'):
            return json.loads(line)
    raise RuntimeError("loader probe produced no result\n" + result.stdout)


def census(path: Path) -> dict[str, Any]:
    top, args = _envelope(path)
    output = _probe(path, args)
    rows: list[dict[str, Any]] = []
    if output == "TIMEOUT":
        rows.append({"module": top, "category": "design", "kind": "loader",
                     "name": top, "status": "REFUSED",
                     "requirement": "loader returned timeout"})
    elif output.startswith("REFUSED\n"):
        rows.append({"module": top, "category": "design", "kind": "loader",
                     "name": top, "status": "REFUSED",
                     "requirement": output.split("\n", 1)[1]})
    elif output.startswith("OK\n"):
        for line in output.splitlines()[1:]:
            fields = line.split(" ", 2)
            if len(fields) == 2:
                kind, name = fields
                detail = "memory" if kind == "MEM" else "declaration"
            elif len(fields) == 3:
                kind, name, detail = fields
            else:
                raise RuntimeError("malformed loader row: " + line)
            category = {
                "MEM": "memory",
                "DECL": "declaration",
                "PROC": "process",
            }.get(kind)
            if category is None:
                raise RuntimeError("unknown loader row: " + line)
            status = "REFUSED" if detail.startswith("REFUSED ") else "ADMITTED"
            requirement = detail.removeprefix("REFUSED ") if status == "REFUSED" else "emitted by CoreMemDesign"
            if kind == "PROC" and detail.startswith("assign"):
                category = "continuous_assign"
            rows.append({"module": top, "category": category, "kind": detail.split(" ", 1)[0],
                         "name": name,
                         "status": status, "requirement": requirement})
    else:
        raise RuntimeError("unknown loader result: " + output)
    counts = {status: sum(row["status"] == status for row in rows) for status in STATUSES}
    return {
        "schema": SCHEMA,
        "top": top,
        "envelope_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
        "counts": counts,
        "refused": counts["REFUSED"],
        "not_reached": counts["NOT REACHED"],
        "remaining": counts["REFUSED"] + counts["NOT REACHED"],
        "rows": rows,
    }


def self_test() -> None:
    """Exercise the loader-backed path on a checked-in small envelope."""

    fixture = ROOT / "Examples/system-verilog/ff_one/cv32e40p_ff_one.sv.json"
    result = census(fixture)
    if not result["rows"]:
        raise AssertionError("loader self-test emitted no rows")
    if result["remaining"] != result["refused"] + result["not_reached"]:
        raise AssertionError("loader census remaining count is inconsistent")
    if any(row["status"] == "NOT REACHED" for row in result["rows"]):
        raise AssertionError("loader census fabricated a reachability status")
    print(
        "core_census --self-test ok: "
        f"{result['counts']['ADMITTED']} admitted, "
        f"{result['counts']['REFUSED']} refused"
    )


def _print(result: dict[str, Any]) -> None:
    print(f"top={result['top']}")
    for row in result["rows"]:
        print(f"{row['status']:11} {row['module']} {row['category']:<18} {row['kind']} {row['name']} :: {row['requirement']}")
    counts = result["counts"]
    print("counts: " + ", ".join(f"{status}={counts[status]}" for status in STATUSES)
          + f"; remaining={result['remaining']}")


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("envelope", type=Path, nargs="?")
    parser.add_argument("--json", dest="json_path", type=Path)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args(argv)
    if args.self_test:
        if args.envelope is not None:
            parser.error("--self-test does not take an envelope")
        try:
            self_test()
        except (OSError, ValueError, RuntimeError, AssertionError) as exc:
            parser.error(str(exc))
        return 0
    if args.envelope is None:
        parser.error("an envelope is required unless --self-test is used")
    try:
        result = census(args.envelope)
    except (OSError, ValueError, RuntimeError) as exc:
        parser.error(str(exc))
    if args.json_path is not None:
        args.json_path.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    _print(result)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
