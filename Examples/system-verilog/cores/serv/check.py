#!/usr/bin/env python3
"""Run the pinned SERV source set against both approved simulators."""

from __future__ import annotations

import hashlib
import os
from pathlib import Path
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


BUS_FIELDS = ("cycle valid order insn pc next_pc rd result icyc iack iaddr idata "
              "dcyc dack we addr sel wdata rdata trap halt intr").split()

# (instruction, PC before/after, destination, write-back value) at retirement.
PROGRAM = [
    (0x00500093, 0, 4, 1, 5),
    (0x00708113, 4, 8, 2, 12),
    (0x002081b3, 8, 12, 3, 17),
    (0x04302023, 12, 16, 0, 0),
    (0x04002203, 16, 20, 4, 17),
    (0x00418463, 20, 28, 0, 0),
    (0x0000006f, 28, 28, 0, 0),
]


def check_program(trace: list[str]) -> None:
    retires = []
    data_transfers = []
    for cycle, line in enumerate(trace):
        row = dict(zip(BUS_FIELDS, line.split()[1:], strict=True))
        if row["cycle"] != str(cycle):
            raise ValueError(f"unexpected SERV cycle at {cycle}")
        if row["dcyc"] == row["dack"] == "1":
            write = int(row["we"], 2)
            value = row["wdata"] if write else row["rdata"]
            data_transfers.append((write, int(row["addr"], 2), int(row["sel"], 2), int(value, 2)))
        if row["valid"] == "1":
            if int(row["order"], 2) != len(retires) or any(
                row[k] != "0" for k in ("trap", "halt", "intr")
            ):
                raise ValueError(f"unexpected SERV retirement order or status at {cycle}")
            retires.append(tuple(int(row[k], 2) for k in ("insn", "pc", "next_pc", "rd", "result")))
    if retires != PROGRAM:
        raise ValueError(f"unexpected SERV retirements: {retires}")
    if data_transfers != [(1, 64, 15, 17), (0, 64, 15, 17)]:
        raise ValueError(f"unexpected SERV data transfers: {data_transfers}")


def main() -> None:
    root_text = os.environ.get("SERV_ROOT")
    if not root_text:
        raise SystemExit("set SERV_ROOT to the pinned SERV checkout")
    root = Path(root_text).resolve()
    commit = run(["git", "rev-parse", "HEAD"], root).strip()
    if commit != PINNED_COMMIT:
        raise SystemExit(f"source commit {commit} is not the pinned {PINNED_COMMIT}")
    if run(["git", "diff", "--name-only", "HEAD", "--", "rtl"], root).strip():
        raise SystemExit("SERV RTL differs from its pinned revision")
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
        for tool, flag, pin in (("iverilog", "-V", "s20250103-64-gdad78d525"),
                                ("xrun", "-version", "24.03-s004")):
            version = run([tool, flag], work).splitlines()[0]
            if pin not in version:
                raise SystemExit(f"unexpected simulator version: {version}")
            print(version)
        run([
            "iverilog", "-g2012", "-DRISCV_FORMAL", "-I", str(root / "rtl"),
            "-s", "serv_rvfi_tb", "-o", str(iverilog), str(testbench),
            *source_text,
        ], work)
        icarus_rows = rows(run(["vvp", str(iverilog)], work))
        bus_iv = [line for line in run(["vvp", str(iverilog), "+wishbone"], work).splitlines()
                  if line.startswith("BUS ")]
        run([
            "xrun", "-elaborate", "-sv", "-q", "-define", "RISCV_FORMAL", "-top",
            "serv_rvfi_tb", str(testbench), *source_text,
        ], work)
        xcelium_rows = rows(run(["xrun", "-R", "-q"], work))
        bus_xc = [line for line in run(["xrun", "-R", "-q", "+wishbone"], work).splitlines()
                  if line.startswith("BUS ")]

    if len(icarus_rows) != EXPECTED_ROWS or len(xcelium_rows) != EXPECTED_ROWS:
        raise SystemExit(
            f"expected {EXPECTED_ROWS} rows, got Icarus={len(icarus_rows)} "
            f"Xcelium={len(xcelium_rows)}"
        )
    if icarus_rows != xcelium_rows:
        raise SystemExit("the pinned simulators disagree on the SERV witness")
    digest = hashlib.sha256(("\n".join(icarus_rows) + "\n").encode()).hexdigest()
    if digest != "bbe7e48c24f4748f96beaf097df899183a5c15c0e7f51cad68d4057a034320ad":
        raise SystemExit("legacy constant-ack trace differs from the recorded rows")
    print(f"legacy constant-ack rows: {EXPECTED_ROWS}/{EXPECTED_ROWS} agree")
    print(f"normalized-row-sha256: {digest}")
    if bus_iv != bus_xc:
        first = next((i for i, (a, b) in enumerate(zip(bus_iv, bus_xc)) if a != b),
                     min(len(bus_iv), len(bus_xc)))
        raise SystemExit(f"Wishbone simulators differ at cycle {first}")
    check_program(bus_iv)
    print(f"Wishbone: {len(bus_iv)} cycles agree, {len(PROGRAM)} checked retirements")


if __name__ == "__main__":
    main()
