#!/usr/bin/env python3
"""Audit the C semantic paths for spelling-based ``CType`` operations.

The F1 gate is deliberately fail-closed. A structured ``QualType`` bridge
may coexist with the legacy alias while migration is in progress, but the
gate must report every remaining type-string operation before F1 can close.
This checker scans only the named C type paths and never inspects corpus
source or parser output. The legacy ``CType := String`` alias is itself a
finding until the declaration and expression constructors carry QualType.
"""

from __future__ import annotations

import argparse
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
PATHS = (
    ROOT / "LeanModels/C/Ast.lean",
    ROOT / "LeanModels/C/Torture.lean",
    ROOT / "LeanModels/C/C23/Expr.lean",
    ROOT / "LeanModels/C/C23/Stmt.lean",
    ROOT / "LeanModels/C/C23/Memory.lean",
)

PATTERNS = (
    re.compile(r"\.(?:startsWith|endsWith|contains|splitOn|dropEnd|trimAscii|drop)\b"),
    re.compile(r"\b(?:intTyOf\??|isPtrType|isPtrIntType|compatiblePointerTypes|normalizeTy)\b"),
    re.compile(r"(?:\b(?:ty|fieldTy|computeLHSType|computeResultType)\s*(?:==|!=)|(?:==|!=)\s*\b(?:ty|fieldTy|computeLHSType|computeResultType))\s*\"(?:_?Bool|char|signed char|unsigned char|short|unsigned short|int|unsigned int|long|unsigned long|long long|unsigned long long|float|double|long double)\""),
)

ALIAS_PATTERN = re.compile(r"abbrev\s+CType\s*:=\s*String")

# The semantic files also manipulate source names, builtin names, and byte
# buffers.  Those are strings, but they are not C type spellings.  Keep the
# audit conservative by excluding only receivers whose surrounding code makes
# their non-type role explicit.  A new or ambiguous receiver remains reported.
NON_TYPE_RECEIVERS = re.compile(
    r"\b(?:nm|name|kind|text|callee|calleeName|allowed|args|es|rest|"
    r"bytes|source\.bytes|target\.bytes|fo\.bytes|string\.bytes|"
    r"c\.bytes|chars|pattern|input|value|raw|spelling|List)\s*\."
)


def findings(paths: tuple[Path, ...] = PATHS) -> list[tuple[str, int, str]]:
    out: list[tuple[str, int, str]] = []
    for path in paths:
        for number, line in enumerate(path.read_text().splitlines(), 1):
            # Kernel guards exercise string/list helpers as data. They are
            # instrumentation, not semantic operations on a C type.
            if line.lstrip().startswith(("#guard", "--")):
                continue
            if (any(pattern.search(line) for pattern in PATTERNS) and
                    not NON_TYPE_RECEIVERS.search(line)):
                out.append((str(path.relative_to(ROOT)), number, line.strip()))
    return out


def legacy_aliases(paths: tuple[Path, ...] = PATHS) -> list[tuple[str, int, str]]:
    out: list[tuple[str, int, str]] = []
    for path in paths:
        for number, line in enumerate(path.read_text().splitlines(), 1):
            if ALIAS_PATTERN.search(line):
                out.append((str(path.relative_to(ROOT)), number, line.strip()))
    return out


def self_test() -> int:
    sample = ROOT / "tools" / ".c-type-string-self-test.lean"
    sample.write_text(
        "abbrev CType := String\n"
        "def typeCase (ty : CType) := ty.endsWith \"*\"\n"
        "def ptrCase (ty : CType) := intTyOf? ty\n"
        "def litCase (ty : CType) := ty == \"float\"\n"
        "def normCase (layout : Layout) (ty : CType) := layout.normalizeTy ty\n"
        "def byteCase (bytes : List Nat) := bytes.drop 1\n"
        "def nameCase (nm : String) := nm.contains \"x\"\n")
    try:
        got = findings((sample,))
        aliases = legacy_aliases((sample,))
        if len(got) != 4 or got[0][1] != 2 or len(aliases) != 1 or aliases[0][1] != 1:
            print("check_c_type_strings --self-test: failed", file=sys.stderr)
            return 1
    finally:
        sample.unlink(missing_ok=True)
    print("check_c_type_strings --self-test: ok")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        return self_test()
    rows = findings()
    aliases = legacy_aliases()
    for path, line, text in rows:
        print(f"{path}:{line}: {text}")
    for path, line, text in aliases:
        print(f"{path}:{line}: legacy CType alias: {text}")
    print(f"check_c_type_strings: {len(rows)} remaining type-string operation(s); "
          f"{len(aliases)} legacy CType alias(es)",
          file=sys.stderr)
    return 1 if rows or aliases else 0


if __name__ == "__main__":
    raise SystemExit(main())
