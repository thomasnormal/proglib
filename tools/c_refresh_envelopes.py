#!/usr/bin/env python3
"""Refresh C corpus envelopes with the approved parser-native probes.

Sources remain in the external corpus cache.  This tool only reruns the
approved extractor; it never parses C text itself.  C1 and C2 source caches
are refreshed in parallel, while rows from other corpora retain their pinned
envelope paths in the copied manifest.
"""

from __future__ import annotations

import argparse
import concurrent.futures
import hashlib
import json
import os
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parent.parent
EXTRACTOR = ROOT / "extractors" / "c" / "extract.py"


def refresh_one(item: dict, source_root: Path, out_root: Path, string_plugin: str,
                layout_plugin: str) -> tuple[str, str | None]:
    source = source_root / item["name"]
    if item.get("status") != "parsed" or not source.is_file():
        return item["name"], None
    digest = hashlib.sha256(source.read_bytes()).hexdigest()
    if digest != item.get("sha256"):
        raise RuntimeError(f"source hash mismatch for {item['name']}")
    output = out_root / (item["name"] + ".json")
    output.parent.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env["LEAN_C_STRING_BYTES_PLUGIN"] = string_plugin
    env["LEAN_C_RECORD_LAYOUT_PLUGIN"] = layout_plugin
    command = [sys.executable, str(EXTRACTOR), str(source),
               "--source-name", item["corpus"] + "/" + item["name"],
               "-o", str(output)]
    result = subprocess.run(command, cwd=ROOT, env=env,
                            capture_output=True, text=True)
    if result.returncode:
        print(f"c_refresh_envelopes: retained {item['name']}: "
              f"current frontend rejected source ({result.stderr.splitlines()[0] if result.stderr else 'no diagnostic'})",
              file=sys.stderr)
        output.unlink(missing_ok=True)
        return item["name"], None
    return item["name"], str(output)


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--manifest", required=True)
    ap.add_argument("--c1-root", required=True)
    ap.add_argument("--c2-root", required=True)
    ap.add_argument("--c3-root")
    ap.add_argument("--out-root", required=True)
    ap.add_argument("--string-plugin", required=True)
    ap.add_argument("--layout-plugin", required=True)
    ap.add_argument("--jobs", type=int, default=4)
    args = ap.parse_args(argv)
    if args.jobs < 1:
        ap.error("--jobs must be positive")
    data = json.loads(Path(args.manifest).read_text())
    out = Path(args.out_root)
    roots = {
        "gcc.c-torture/execute": Path(args.c1_root),
        "c-testsuite/single-exec": Path(args.c2_root),
    }
    if args.c3_root:
        roots["gcc.c23-run"] = Path(args.c3_root)
    tasks = [(i, roots.get(item.get("corpus")))
             for i, item in enumerate(data.get("tests", []))
             if item.get("corpus") in roots]
    def run(task):
        i, source_root = task
        item = data["tests"][i]
        return i, refresh_one(item, source_root, out / item["corpus"].replace("/", "_"),
                              args.string_plugin, args.layout_plugin)
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.jobs) as pool:
        for i, (_, path) in pool.map(run, tasks):
            if path is not None:
                data["tests"][i]["envelope"] = path
    Path(args.manifest).with_name(Path(args.manifest).stem + "-fresh.json").write_text(
        json.dumps(data, indent=1, sort_keys=True) + "\n")
    print("c_refresh_envelopes: refreshed %d C1/C2 parsed rows" %
          sum(1 for _, root in tasks if root is not None))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
