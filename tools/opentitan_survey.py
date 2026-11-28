#!/usr/bin/env python3
"""Survey OpenTitan primitives and small IPs through the ordinary SV route.

The source checkout is supplied explicitly so the committed table carries no
private filesystem path. Slang performs module discovery and extraction. The
Lean runner performs envelope parsing, ordinary admission, initial-state
construction, and one canonical-E step in one process.
"""

from concurrent.futures import ThreadPoolExecutor, as_completed
import argparse
import collections
import datetime
import json
from pathlib import Path
import re
import subprocess

import pyslang
from pyslang.ast import Compilation
from pyslang.syntax import SyntaxTree

ROOT = Path(__file__).resolve().parents[1]
SUBTREES = (
    "hw/ip/prim/rtl",
    "hw/ip/uart/rtl",
    "hw/ip/spi_host/rtl",
    "hw/ip/spi_device/rtl",
    "hw/ip/i2c/rtl",
    "hw/ip/gpio/rtl",
    "hw/ip/rv_timer/rtl",
    "hw/ip/aon_timer/rtl",
    "hw/ip/pwm/rtl",
)


def candidates(source_root):
    result = []
    for subtree in SUBTREES:
        directory = source_root / subtree
        if not directory.exists():
            continue
        for source in sorted(directory.glob("*.sv")):
            tree = SyntaxTree.fromFile(str(source))
            compilation = Compilation()
            compilation.addSyntaxTree(tree)
            for instance in compilation.getRoot().topInstances:
                result.append((instance.name, source, directory))
    return result


def extract_one(item, source_root, envelope_root):
    top, source, directory = item
    output = envelope_root / f"{top}.json"
    command = [
        "python3", "extractors/sv/extract.py", "--top", top,
        "-I", str(directory), "-I", str(source_root / "hw/ip/prim/rtl"),
        "-o", str(output), str(source),
    ]
    try:
        completed = subprocess.run(
            command, cwd=ROOT, text=True, capture_output=True, timeout=90
        )
    except subprocess.TimeoutExpired:
        return {
            "top": top, "source": source.relative_to(source_root).as_posix(),
            "extracts": False, "error": "extractor timeout after 90 seconds",
        }
    if completed.returncode or not output.exists():
        return {
            "top": top, "source": source.relative_to(source_root).as_posix(),
            "extracts": False,
            "error": (completed.stderr or completed.stdout)[-1000:],
        }
    envelope = json.loads(output.read_text())
    unsupported = []

    def walk(value):
        if isinstance(value, dict):
            if value.get("kind") == "Unsupported":
                unsupported.append((value.get("sv_kind", "Unsupported"), value.get("text", "")))
            for child in value.values():
                walk(child)
        elif isinstance(value, list):
            for child in value:
                walk(child)

    walk(envelope)
    return {
        "top": top, "source": source.relative_to(source_root).as_posix(),
        "extracts": True, "envelope": str(output),
        "extractor_refusal": unsupported[0] if unsupported else None,
        "extractor_walls": unsupported,
    }


def family(row):
    status = row.get("ordinary", "EXTRACTOR:timeout")
    if status.startswith("ADMITTED|"):
        return "admitted"
    if status.startswith("INITIAL_"):
        return "initial-state"
    if status.startswith("EXTRACTOR"):
        return "extractor-timeout"
    message = status.split("|", 1)[1]
    if message.startswith("parameter arity"):
        return "parameter arity"
    if message.startswith("localparam ") or message.startswith("generate bound"):
        return "constant evaluation"
    if message.startswith("generate if"):
        return "generate parameter"
    if message.startswith("GenerateDecl:"):
        return "generate naming"
    if message.startswith("Schedule:"):
        return "scheduling"
    if message.startswith("Event:"):
        return "event scheduling"
    if message.startswith("NetSymbol:"):
        return "net metadata"
    if message.startswith("E memory route does not yet admit module member"):
        match = re.search(r"module member '([^:']+)", message)
        return "module member " + (match.group(1) if match else "unsupported")
    return message.split(":", 1)[0]


def detail(row):
    status = row.get("ordinary")
    if not status:
        return "extractor timeout"
    message = status.split("|", 1)[1] if "|" in status else status
    message = message.replace("\n", " ")
    return message[:260] + ("…" if len(message) > 260 else "")


def wall_family_from_tag(tag):
    """Group parser walls by the Slang node family that caused them."""
    if not tag:
        return "unknown"
    return tag.split(":", 1)[0]


def all_walls(row):
    """Return parser-visible walls plus the ordinary route's first wall."""
    walls = []
    for tag, text in row.get("extractor_walls", []):
        if tag and tag not in walls:
            walls.append(tag)
    ordinary = row.get("ordinary", "")
    if ordinary and not ordinary.startswith("ADMITTED|"):
        message = ordinary.split("|", 1)[1] if "|" in ordinary else ordinary
        label = f"ordinary: {family(row)}"
        if label not in walls:
            walls.append(label)
    if not walls and row.get("extracts") is False:
        walls.append("extractor timeout")
    return walls


def classify(rows):
    for row in rows:
        status = row.get("ordinary", "")
        if status.startswith("ADMITTED|"):
            row.update(loads="YES", step="YES", profile="YES")
        elif status.startswith("INITIAL_"):
            row.update(loads="YES", step="NO", profile="NO")
        else:
            row.update(loads="NO", step="NO", profile="NO")
        row["family"] = family(row)
        row["detail"] = detail(row)
        row["all_walls"] = all_walls(row)
        row["wall_families"] = sorted({
            wall_family_from_tag(tag)
            for tag, _text in row.get("extractor_walls", [])
        } | ({row["family"]} if row["loads"] == "NO" else set()))


def render(rows, commit):
    families = collections.Counter(row["family"] for row in rows)
    wall_modules = collections.Counter()
    sole_walls = collections.Counter()
    for row in rows:
        if row["loads"] == "YES":
            continue
        groups = set(row["wall_families"])
        for group in groups:
            wall_modules[group] += 1
        if len(groups) == 1:
            sole_walls[next(iter(groups))] += 1
    lines = [
        "# OpenTitan primitive and small-IP survey", "",
        f"Pinned source: `lowRISC/opentitan` at commit `{commit}` from "
        "`https://github.com/lowRISC/opentitan.git`. The checkout was fetched "
        "outside this repository. Its top-level `LICENSE` is Apache-2.0. "
        "The survey date is 2026-11-27.", "",
        "The survey covers every module Slang exposes from "
        "`hw/ip/prim/rtl/*.sv` and the available RTL directories for "
        "`uart`, `spi_host`, `spi_device`, `i2c`, `gpio`, `rv_timer`, "
        "`aon_timer`, and `pwm`. Each source was extracted with the approved "
        "Slang frontend, loaded through the ordinary `load_design_sv2` "
        "admission path, and, when admitted, given one empty-input "
        "`CoreMemDesign.step` call. Sources that timed out during extraction "
        "remain explicit rows. No source was changed and no simulator result "
        "is claimed by this survey. The measurement date is "
        f"{datetime.datetime.now(datetime.timezone.utc).date().isoformat()}.",
        "", "## Counts", "",
        "| outcome | count |", "| --- | ---: |",
        f"| modules surveyed | {len(rows)} |",
        f"| extracts | {sum(row.get('extracts', False) for row in rows)} |",
        f"| ordinary loads | {sum(row['loads'] == 'YES' for row in rows)} |",
        f"| one-cycle steps | {sum(row['step'] == 'YES' for row in rows)} |",
        f"| profile admitted | {sum(row['profile'] == 'YES' for row in rows)} |", "",
        "First-wall families are counted by the ordinary-route diagnostic. The all-wall table also includes every parser-visible Unsupported node.", "",
        "| family | count |", "| --- | ---: |",
    ]
    for key, count in sorted(families.items()):
        if key != "admitted":
            lines.append(f"| {key} | {count} |")
    lines += ["", "## All-wall feature families", "",
              "Counts use refused modules as the denominator. `modules` counts every refused module exposing the family, and `sole-wall` counts modules exposing that family only.", "",
              "| feature family | modules | sole-wall |", "| --- | ---: | ---: |"]
    for key in sorted(wall_modules):
        lines.append(f"| {key} | {wall_modules[key]} | {sole_walls[key]} |")
    lines += ["", "## Module rows", "",
              "| area | module | source | extracts | loads | one cycle | profile | first refusal | all walls |",
              "| --- | --- | --- | :---: | :---: | :---: | :---: | --- | --- |"]
    for row in rows:
        area = row["source"].split("/")[2]
        message = row["detail"].replace("|", "\\|")
        walls = "<br>".join(wall.replace("|", "\\|") for wall in row["all_walls"])
        lines.append(
            f"| {area} | `{row['top']}` | `{row['source']}` | "
            f"{'YES' if row.get('extracts') else 'NO'} | {row['loads']} | "
            f"{row['step']} | {row['profile']} | {message} | {walls} |"
        )
    return "\n".join(lines) + "\n"


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("source_root", type=Path)
    parser.add_argument("--commit", required=True)
    parser.add_argument("--output", type=Path, default=ROOT / "docs/sv-opentitan-survey.md")
    args = parser.parse_args()
    envelope_root = args.output.parent / ".opentitan-survey-envelopes"
    envelope_root.mkdir(parents=True, exist_ok=True)
    items = candidates(args.source_root)
    rows = []
    with ThreadPoolExecutor(max_workers=8) as pool:
        futures = [pool.submit(extract_one, item, args.source_root, envelope_root) for item in items]
        for future in as_completed(futures):
            rows.append(future.result())
    rows.sort(key=lambda row: row["top"])
    envelopes = [row["envelope"] for row in rows if row.get("extracts")]
    runner = ROOT / "tools/opentitan_survey_runner.lean"
    completed = subprocess.run(
        ["lake", "env", "lean", "--run", str(runner), *envelopes],
        cwd=ROOT, text=True, capture_output=True, check=False, timeout=900,
    )
    if completed.returncode:
        raise SystemExit(completed.stderr)
    outcomes = {}
    for line in completed.stdout.splitlines():
        if "|" in line:
            path, status = line.split("|", 1)
            outcomes[path] = status
    for row in rows:
        if row.get("envelope") in outcomes:
            row["ordinary"] = outcomes[row["envelope"]]
    classify(rows)
    args.output.write_text(render(rows, args.commit))
    print(json.dumps({"modules": len(rows), "families": collections.Counter(row["family"] for row in rows)}, indent=2))


if __name__ == "__main__":
    main()
