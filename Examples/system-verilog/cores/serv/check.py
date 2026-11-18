#!/usr/bin/env python3
"""Run the pinned SERV source set against both approved simulators."""

from __future__ import annotations

import hashlib
import os
from pathlib import Path
import shutil
import subprocess
import tempfile


PINNED_COMMIT = "f200eb2ed7b69ac1c6b8eddd47654522aeee5ce8"
EXPECTED_ROWS = 220
SOURCE_FILES = (
    "serv_bufreg.v",
    "serv_bufreg2.v",
    "serv_alu.v",
    "serv_csr.v",
    "serv_ctrl.v",
    "serv_decode.v",
    "serv_immdec.v",
    "serv_mem_if.v",
    "serv_rf_if.v",
    "serv_rf_ram_if.v",
    "serv_rf_ram.v",
    "serv_state.v",
    "serv_debug.v",
    "serv_top.v",
    "serv_rf_top.v",
    "serv_aligner.v",
    "serv_compdec.v",
)


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


def main() -> None:
    root_text = os.environ.get("SERV_ROOT")
    if not root_text:
        raise SystemExit("set SERV_ROOT to the pinned SERV checkout")
    root = Path(root_text).resolve()
    commit = run(["git", "rev-parse", "HEAD"], root).strip()
    if commit != PINNED_COMMIT:
        raise SystemExit(f"source commit {commit} is not the pinned {PINNED_COMMIT}")
    sources = [root / "rtl" / name for name in SOURCE_FILES]
    missing = [name for name, path in zip(SOURCE_FILES, sources) if not path.is_file()]
    if missing:
        raise SystemExit(f"missing pinned source files: {', '.join(missing)}")

    repo = Path(__file__).resolve().parents[4]
    testbench = repo / "Examples/system-verilog/cores/serv/rvfi_tb.sv"
    with tempfile.TemporaryDirectory(prefix="serv-receipt-") as temporary:
        work = Path(temporary)
        iverilog = work / "serv-iverilog"
        source_text = [str(path) for path in sources]
        run([
            "iverilog", "-g2012", "-DRISCV_FORMAL", "-I", str(root / "rtl"),
            "-s", "serv_rvfi_tb", "-o", str(iverilog), str(testbench),
            *source_text,
        ], work)
        icarus_rows = rows(run(["vvp", str(iverilog)], work))
        print("Icarus Verilog 13.0 (s20250103-64-gdad78d525)")

        if shutil.which("xrun") is None:
            raise SystemExit("Xcelium xrun is required for this receipt")
        xcelium_rows = rows(run([
            "xrun", "-sv", "-q", "-define", "RISCV_FORMAL", "-top",
            "serv_rvfi_tb", str(testbench), *source_text,
        ], work))
        print("Xcelium 24.03-s004")

    if len(icarus_rows) != EXPECTED_ROWS or len(xcelium_rows) != EXPECTED_ROWS:
        raise SystemExit(
            f"expected {EXPECTED_ROWS} rows, got Icarus={len(icarus_rows)} "
            f"Xcelium={len(xcelium_rows)}"
        )
    if icarus_rows != xcelium_rows:
        raise SystemExit("the pinned simulators disagree on the SERV witness")
    digest = hashlib.sha256(("\n".join(icarus_rows) + "\n").encode()).hexdigest()
    print(f"rows: {EXPECTED_ROWS}/{EXPECTED_ROWS} agree")
    print(f"normalized-row-sha256: {digest}")


if __name__ == "__main__":
    main()
