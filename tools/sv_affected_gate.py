#!/usr/bin/env python3
"""Build every SV example affected by the branch's changed Lean modules.

The short push gate is intentionally curated.  This gate derives the
transitive import closure from the selected git base, so a library change
cannot pass because an example was omitted from a hand-maintained list.
"""

from __future__ import annotations

import argparse
import re
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
IMPORT_RE = re.compile(r"^\s*import\s+([^\s]+)", re.MULTILINE)


def module_parts(path: Path) -> tuple[str, ...]:
    return tuple(path.relative_to(ROOT).with_suffix("").parts)


def module_key(parts: tuple[str, ...]) -> tuple[str, ...]:
    """Canonical module components, independent of Lean identifier quoting."""
    return tuple(part.strip("«»") for part in parts)


def imported_parts(token: str) -> tuple[str, ...]:
    return module_key(tuple(token.split(".")))


def lake_name(parts: tuple[str, ...]) -> str:
    return ".".join(f"«{part}»" if not part.isidentifier() else part for part in parts)


def changed_modules(base: str) -> set[tuple[str, ...]]:
    names = subprocess.check_output(
        [
            "git",
            "diff",
            "--name-only",
            f"{base}...HEAD",
            "--",
            "LeanModels/Sv",
            "Examples/system-verilog",
        ],
        cwd=ROOT,
        text=True,
    ).splitlines()
    result = set()
    for name in names:
        path = ROOT / name
        if path.suffix == ".lean" and path.exists():
            result.add(module_key(module_parts(path)))
    return result


def affected_targets(base: str) -> list[str]:
    files = list((ROOT / "LeanModels/Sv").rglob("*.lean"))
    files += list((ROOT / "Examples/system-verilog").rglob("*.lean"))
    paths = {module_key(module_parts(path)): path for path in files}
    imports = {name: [] for name in paths}
    for name, path in paths.items():
        text = path.read_text(encoding="utf-8", errors="replace")
        imports[name] = [
            item
            for item in (imported_parts(token) for token in IMPORT_RE.findall(text))
            if item in paths
        ]

    changed = changed_modules(base)
    unknown = sorted(changed - paths.keys())
    if unknown:
        raise RuntimeError("changed Lean modules are not present: " + ", ".join(map(lake_name, unknown)))
    if not changed:
        raise RuntimeError(f"no changed Lean modules under the selected base {base}")

    reverse = {name: [] for name in paths}
    for name, dependencies in imports.items():
        for dependency in dependencies:
            reverse[dependency].append(name)
    seen = set(changed)
    pending = list(changed)
    while pending:
        current = pending.pop()
        for dependent in reverse[current]:
            if dependent not in seen:
                seen.add(dependent)
                pending.append(dependent)

    return sorted(
        lake_name(name)
        for name in seen
        if name[:2] == ("Examples", "system-verilog")
    )


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--base",
        default="origin/master",
        help="git revision to compare with (default: origin/master)",
    )
    parser.add_argument("--build", action="store_true", help="build the computed targets with lake")
    parser.add_argument("--list", action="store_true", help="print every computed target")
    args = parser.parse_args()
    try:
        targets = affected_targets(args.base)
    except (OSError, subprocess.CalledProcessError, RuntimeError) as exc:
        parser.error(str(exc))
    print("sv-affected-target-gate: %d target(s)" % len(targets))
    if args.list:
        print("\n".join(targets))
    if not args.build:
        return 0
    if not targets:
        print("sv-affected-target-gate: no targets collected", flush=True)
        return 1
    return subprocess.run(["lake", "build", *targets], cwd=ROOT).returncode


if __name__ == "__main__":
    raise SystemExit(main())
