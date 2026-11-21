#!/usr/bin/env python3
"""Double-run the parser-native C QualType observation probe.

The probe is the pinned Clang frontend's source of type structure. This
harness checks byte-identical output and validates every recursive case that
the envelope ingester accepts. It never parses a type spelling.
"""

import argparse
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile


def validate_type(value):
    if not isinstance(value, dict) or not isinstance(value.get("kind"), str):
        raise RuntimeError(f"invalid structured type: {value!r}")
    kind = value["kind"]
    if kind == "builtin":
        if not isinstance(value.get("name"), str) or not value["name"]:
            raise RuntimeError(f"invalid builtin type: {value!r}")
    elif kind == "pointer":
        validate_type(value.get("pointee"))
    elif kind == "array":
        validate_type(value.get("element"))
        extent = value.get("extent")
        if extent is not None and (type(extent) is not int or extent < 0):
            raise RuntimeError(f"invalid array extent: {value!r}")
    elif kind == "qualified":
        if type(value.get("const")) is not bool or type(value.get("volatile")) is not bool:
            raise RuntimeError(f"invalid qualifiers: {value!r}")
        if not value["const"] and not value["volatile"]:
            raise RuntimeError(f"empty qualifiers: {value!r}")
        validate_type(value.get("base"))
    elif kind == "function":
        validate_type(value.get("result"))
        if not isinstance(value.get("parameters"), list):
            raise RuntimeError(f"invalid function parameters: {value!r}")
        for parameter in value["parameters"]:
            validate_type(parameter)
        if type(value.get("variadic")) is not bool:
            raise RuntimeError(f"invalid variadic bit: {value!r}")
    elif kind in ("record", "enumeration", "typedef"):
        declaration = value.get("declaration")
        if (not isinstance(declaration, dict) or
                not isinstance(declaration.get("id"), str) or
                not declaration["id"]):
            raise RuntimeError(f"invalid declaration identity: {value!r}")
    elif kind == "unsupported":
        if not isinstance(value.get("reason"), str) or not value["reason"]:
            raise RuntimeError(f"unsupported type has no reason: {value!r}")
    else:
        raise RuntimeError(f"unsupported structured type kind: {kind!r}")


def run(clang, plugin, source):
    command = [clang, "--no-default-config", "-std=c23", "-fsyntax-only",
               "-Xclang", "-load", "-Xclang", plugin,
               "-Xclang", "-add-plugin", "-Xclang", "lean-c-structured-types",
               str(source)]
    result = subprocess.run(command, capture_output=True, text=False)
    if result.returncode:
        raise RuntimeError(result.stderr.decode("utf-8", "replace"))
    marker = b"LEAN_C_STRUCTURED_TYPES="
    records = [line[len(marker):] for line in result.stderr.splitlines()
               if line.startswith(marker)]
    if len(records) != 1:
        raise RuntimeError("probe did not emit exactly one structured stderr record")
    try:
        document = json.loads(records[0].decode("utf-8"))
    except (UnicodeDecodeError, json.JSONDecodeError) as error:
        raise RuntimeError(f"probe output is not one JSON document: {error}")
    if not isinstance(document, list):
        raise RuntimeError("probe output is not an array")
    for record in document:
        if (not isinstance(record, dict) or record.get("kind") not in
                ("StructuredType", "StructuredExprType") or
                type(record.get("offset")) is not int or record["offset"] < 0):
            raise RuntimeError(f"invalid structured type record: {record!r}")
        if record["kind"] == "StructuredExprType":
            if (type(record.get("end_offset")) is not int or
                    record["end_offset"] < record["offset"] or
                    not isinstance(record.get("expr_kind"), str) or
                    not record["expr_kind"]):
                raise RuntimeError(f"invalid structured expression identity: {record!r}")
        validate_type(record.get("type"))
    ids = {}
    def canonical(value):
        if isinstance(value, dict):
            out = {}
            for key, item in value.items():
                if key in ("id", "decl_id", "expr_id") and isinstance(item, str) and item.startswith("0x"):
                    item = ids.setdefault(item, "id" + str(len(ids)))
                out[key] = canonical(item)
            return out
        if isinstance(value, list):
            return [canonical(item) for item in value]
        return value
    normalized = canonical(document)
    return json.dumps(normalized, sort_keys=True, separators=(",", ":")).encode(), normalized


def self_test():
    records = [
        {"kind": "StructuredType", "offset": 0,
         "type": {"kind": "builtin", "name": "int"}},
        {"kind": "StructuredType", "offset": 4,
         "type": {"kind": "pointer", "pointee": {"kind": "array",
             "element": {"kind": "builtin", "name": "char"}, "extent": 4}}},
        {"kind": "StructuredType", "offset": 6,
         "type": {"kind": "array",
             "element": {"kind": "builtin", "name": "int"}, "extent": None}},
        {"kind": "StructuredType", "offset": 8,
         "type": {"kind": "record", "declaration": {"id": "decl-12"}}},
        {"kind": "StructuredExprType", "offset": 16, "end_offset": 19,
         "expr_kind": "ArraySubscriptExpr",
         "type": {"kind": "builtin", "name": "unsigned char"}},
    ]
    for record in records:
        validate_type(record["type"])
    try:
        validate_type({"kind": "record", "declaration": {"id": ""}})
    except RuntimeError:
        pass
    else:
        raise RuntimeError("empty declaration identity was accepted")
    try:
        validate_type({"kind": "StructuredExprType", "offset": 4,
                       "end_offset": 3, "expr_kind": "ArraySubscriptExpr",
                       "type": {"kind": "builtin", "name": "int"}})
    except RuntimeError:
        pass
    else:
        raise RuntimeError("backward expression range was accepted")
    print("c_structured_type_determinism: self-test ok")
    return 0


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("source", type=Path, nargs="?")
    parser.add_argument("--plugin")
    parser.add_argument("--clang", default=os.environ.get("LEAN_C_CLANG", "clang"))
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    try:
        if args.self_test:
            return self_test()
        if args.source is None or not args.plugin:
            parser.error("source and --plugin are required unless --self-test is used")
        first_bytes, first = run(args.clang, args.plugin, args.source)
        second_bytes, second = run(args.clang, args.plugin, args.source)
    except RuntimeError as error:
        print(f"c_structured_type_determinism: {error}", file=sys.stderr)
        return 1
    if first_bytes != second_bytes or first != second:
        print("c_structured_type_determinism: two probe runs differ", file=sys.stderr)
        return 1
    print(f"c_structured_type_determinism: ok ({len(first)} records)")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
