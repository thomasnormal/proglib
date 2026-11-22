#!/usr/bin/env python3
"""Check a four-state load, register writeback and store on the pinned core."""
from hashlib import sha256
from pathlib import Path
import subprocess

import battery_check as battery
from check import run_receipt


HERE = Path(__file__).resolve().parent
CYCLES = 32
WORD = "x" * 24 + "10100101"


def main() -> None:
    for tool, flag, pin in (("iverilog", "-V", "s20250103-64-gdad78d525"),
                            ("xrun", "-version", "24.03-s004")):
        version = subprocess.check_output([tool, flag], text=True, stderr=subprocess.STDOUT)
        if pin not in version.splitlines()[0]:
            raise SystemExit(f"unexpected {tool} version: {version.splitlines()[0]}")
        print(version.splitlines()[0])
    if sha256(battery.ENVELOPE.read_bytes()).hexdigest() != battery.PINNED_ENVELOPE:
        raise SystemExit("DarkRISCV envelope pin differs")

    lines, _ = run_receipt(HERE / "x_register_tb.sv", "darkriscv_x_register_tb", CYCLES)
    if lines != (HERE / "x_register_transcript.txt").read_text().splitlines():
        raise SystemExit("live simulator rows differ from the transcript")
    rows = battery.expected_rows(lines, CYCLES, observe_x2=True)
    samples = [dict(row) for row in rows]
    load = next(i for i, r in enumerate(samples)
                if r["DDREQ"] == r["DRD"] == "1" and int(r["DADDR"], 2) == 0)
    store = next(i for i, r in enumerate(samples)
                 if i > load and r["DDREQ"] == r["DWR"] == "1" and int(r["DADDR"], 2) == 4)
    if (samples[load]["REGS[2]"] != "0" * 32 or samples[load]["DATAI"] != WORD
            or any(r["REGS[2]"] != WORD for r in samples[load + 1:])
            or samples[store]["DATAO"] != WORD):
        raise SystemExit("missing x2 load, retention, or store observation")

    corrupted = rows.copy()
    corrupted[store] = [(name, value.replace("x", "0", 1) if name == "REGS[2]" else value)
                        for name, value in rows[store]]
    ok, accepts_corruption, difference = battery.run_lean(rows, corrupted)
    if not ok or accepts_corruption:
        raise SystemExit(f"Lean agreement={ok}, first difference={difference}, "
                         f"accepted changed x2 bit={accepts_corruption}")
    print(f"{CYCLES}/{CYCLES} three-way cycles; x2 written at {load + 1}, store at {store}; "
          "single x-to-0 register-bit corruption rejected")


if __name__ == "__main__":
    main()
