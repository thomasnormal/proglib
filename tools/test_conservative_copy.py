#!/usr/bin/env python3
"""Check that the copied executor block still matches the merge-base block."""

from pathlib import Path
import subprocess
import sys


ROOT = Path(__file__).resolve().parent.parent
SOURCE = ROOT / "LeanModels/Sv/Kernel/CoreMemExec.lean"
COPY = ROOT / "LeanModels/Sv/Kernel/Conservative.lean"


def git(*args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True)


def block(source: str, start: str, end: str) -> str:
    begin = source.index(start)
    finish = source.index(end, begin)
    return source[begin:finish]


def renamed_merge_base_block(source: str) -> str:
    entry = source.index("def CoreMemDesign.execStmtFuel")
    mutual = source.rfind("mutual\n", 0, entry)
    end = source.index("\nend\n\ndef CoreMemDesign.execStmt", entry)
    result = source[mutual:end]
    for old, new in (
        ("CoreMemDesign.execStmtFuel", "oldStmtFuel"),
        ("CoreMemDesign.execStmtsFuel", "oldStmtsFuel"),
        ("CoreMemDesign.execLoopValuesFuel", "oldLoopFuel"),
        ("E.execStmtFuel", "oldStmtFuel E"),
        ("E.execStmtsFuel", "oldStmtsFuel E"),
        ("E.execLoopValuesFuel", "oldLoopFuel E"),
    ):
        result = result.replace(old, new)
    return result


def main() -> int:
    merge_base = git("merge-base", "HEAD", "origin/master").strip()
    merge_source = git("show", f"{merge_base}:LeanModels/Sv/Kernel/CoreMemExec.lean")
    copied_source = COPY.read_text()
    marker = copied_source.index("-- BEGIN MERGE-BASE (")
    copied = block(copied_source[marker:], "\nmutual\n", "\nend\n\ndef oldExecStmt")
    copied = copied.lstrip("\n")
    expected = renamed_merge_base_block(merge_source)
    entry = "oldStmtFuel E env elems st [] 4096 stmt"
    if copied != expected or entry not in copied_source:
        print(f"Conservative merge-base block differs from {merge_base}", file=sys.stderr)
        return 1
    print(f"Conservative merge-base block matches {merge_base}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
