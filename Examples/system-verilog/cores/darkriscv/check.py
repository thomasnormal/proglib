#!/usr/bin/env python3
"""Run the pinned DarkRISCV simulator witness with both approved simulators."""

from __future__ import annotations

import hashlib
import os
import re
from pathlib import Path
import shutil
import subprocess
import tempfile


PINNED_COMMIT = "bb6b483cc61a2886a0602c7e62b14f5995ddfbb9"
SOURCE_SHA256 = "46d57b15cc42c0458e02500a2a30371cd4e7979970c27afd9d47c40d1fa8c1a0"
EXPECTED_ROWS = 1000


def run(command: list[str], cwd: Path) -> str:
    result = subprocess.run(
        command,
        cwd=cwd,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    return result.stdout


def rows(output: str) -> list[str]:
    return [line for line in output.splitlines() if line.startswith("ROW ")]


def first_difference(left: list[str], right: list[str]) -> str:
    for index, (lhs, rhs) in enumerate(zip(left, right)):
        if lhs == rhs:
            continue
        lhs_fields = dict(re.findall(r"(\w+)=([^ ]+)", lhs))
        rhs_fields = dict(re.findall(r"(\w+)=([^ ]+)", rhs))
        for name in sorted(set(lhs_fields) | set(rhs_fields)):
            if lhs_fields.get(name) != rhs_fields.get(name):
                return (
                    f"cycle {index}, field {name}: "
                    f"Icarus={lhs_fields.get(name, '<missing>')} "
                    f"Xcelium={rhs_fields.get(name, '<missing>')}"
                )
        return f"cycle {index}: row text differs"
    if len(left) != len(right):
        return f"row count differs: Icarus={len(left)} Xcelium={len(right)}"
    return "no difference"


def run_receipt() -> tuple[list[str], list[str]]:
    root_text = os.environ.get("DARKRISCV_ROOT")
    root = (Path(root_text).resolve() if root_text else Path(__file__).with_name("rtl").parent)
    source = root / "rtl" / "darkriscv.v"
    if not source.is_file():
        raise SystemExit(f"missing pinned source: {source}")
    bundled = root == Path(__file__).resolve().parent
    if not bundled:
        commit = run(["git", "rev-parse", "HEAD"], root).strip()
        if commit != PINNED_COMMIT:
            raise SystemExit(f"source commit {commit} is not the pinned {PINNED_COMMIT}")
    source_sha = hashlib.sha256(source.read_bytes()).hexdigest()
    if source_sha != SOURCE_SHA256:
        raise SystemExit(f"source SHA-256 {source_sha} is not the pinned {SOURCE_SHA256}")

    repo = Path(__file__).resolve().parents[4]
    testbench_text = os.environ.get("DARKRISCV_TESTBENCH")
    testbench = (Path(testbench_text).resolve() if testbench_text
                 else repo / "Examples/system-verilog/cores/darkriscv/nop_tb.sv")
    top = os.environ.get("DARKRISCV_TOP", "darkriscv_nop_tb")
    with tempfile.TemporaryDirectory(
        prefix="darkriscv-receipt-",
        dir=os.environ.get("TMPDIR"),
    ) as temporary:
        work = Path(temporary)
        (work / "rtl").symlink_to(root / "rtl", target_is_directory=True)
        sim_work = work / "sim"
        sim_work.mkdir()
        iverilog = work / "darkriscv-iverilog"
        run([
            "iverilog", "-g2012", "-I", str(root / "rtl"), "-o", str(iverilog),
            str(testbench), str(source),
        ], sim_work)
        icarus_rows = rows(run(["vvp", str(iverilog)], sim_work))

        if shutil.which("xrun") is None:
            raise SystemExit("Xcelium xrun is required for this receipt")
        xcelium_rows = rows(run([
            "xrun", "-sv", "-q", "-I../rtl", "-top",
            top, str(testbench), str(source),
        ], sim_work))

    if len(icarus_rows) != EXPECTED_ROWS or len(xcelium_rows) != EXPECTED_ROWS:
        raise SystemExit(
            f"expected {EXPECTED_ROWS} rows, got Icarus={len(icarus_rows)} "
            f"Xcelium={len(xcelium_rows)}"
        )
    if icarus_rows != xcelium_rows:
        raise SystemExit(
            "the pinned simulators disagree on the 1000-cycle witness: "
            + first_difference(icarus_rows, xcelium_rows)
        )
    return icarus_rows, xcelium_rows


def main() -> None:
    icarus_rows, xcelium_rows = run_receipt()
    print("Icarus Verilog 13.0 (s20250103-64-gdad78d525)")
    print("Xcelium 24.03-s004")
    digest = hashlib.sha256(("\n".join(icarus_rows) + "\n").encode()).hexdigest()
    print(f"rows: {EXPECTED_ROWS}/{EXPECTED_ROWS} agree")
    print(f"normalized-row-sha256: {digest}")


if __name__ == "__main__":
    main()
