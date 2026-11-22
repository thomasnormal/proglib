#!/usr/bin/env python3
"""Compare every PicoRV32 output after each rising edge, including reset."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCE = HERE / "picorv32_r2.v"
ENVELOPE = HERE / "picorv32_r2.sv.json"
TESTBENCH = HERE / "rvfi_long_e_probe.v"
TRANSCRIPT = HERE / "pico_simulator_transcript.txt"
REPLAY = ROOT / "harness/rv/picorv32_input_replay.lean"
SOURCE_SHA256 = "0836050971b3c6cdd28ac3b1e5719a67fb645161912bef1e472e63995ceb0622"
ENVELOPE_SHA256 = "17ea7b66ab8ea9b6844c317928f0430cff8b8a5b53f658f7a929bf1aa6cdc236"
TESTBENCH_SHA256 = "9c9ab2cd5f91849bcc19b8cb81ab828da1082ce55d14b3716b24ea012a83e87a"
TRANSCRIPT_SHA256 = "7eaef1b04e2fa561b6de06cca91a96d3148a1ab9858cf10a3f07dcf259c31721"
EXPECTED_LOAD_REFUSAL = (
    "Schedule:preemptive: IEEE 1800-2023 §4.7 permits suspension between "
    "blocking writes; canonical E refuses a multi-write reactive process "
    "whose intermediate value another process can read"
)
RESET_CYCLES = 4
CASE_CYCLES = {"program": 300, "counters": 23}
ICARUS_PIN = "s20250103-64-gdad78d525"
XCELIUM_PIN = "24.03-s004"


def run(command: list[str | Path], cwd: Path, timeout: int | None = 900) -> str:
    result = subprocess.run(command, cwd=cwd, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=timeout)
    if result.returncode:
        raise RuntimeError(f"{command[0]} exited {result.returncode}\n{result.stdout[-4000:]}")
    return result.stdout


def port_widths() -> tuple[dict[str, int], dict[str, int]]:
    envelope = json.loads(ENVELOPE.read_text())
    top = next(m for m in envelope["design"]["modules"] if m["name"] == "picorv32")
    inputs = {p["name"]: p["width"]["resolved"] for p in top["ports"] if p["dir"] == "in"}
    outputs = {p["name"]: p["width"]["resolved"] for p in top["ports"] if p["dir"] == "out"}
    return inputs, outputs


def parse_rows(lines: list[str], schema: dict[str, int], active: int) -> list[dict[str, str]]:
    if len(lines) != RESET_CYCLES + active:
        raise ValueError(f"expected {RESET_CYCLES} reset and {active} active samples, got {len(lines)}")
    rows = []
    for cycle, line in enumerate(lines, -RESET_CYCLES):
        tag, index, *fields = line.split()
        if (tag, index) != ("CYCLE", str(cycle)):
            raise ValueError(f"cycle {cycle}: bad row number {index}")
        row = dict(field.split("=", 1) for field in fields)
        if row.keys() != schema.keys() or len(row) != len(fields):
            raise ValueError(f"cycle {cycle}: missing, extra or duplicate trace field")
        for name, width in schema.items():
            if len(row[name]) != width or set(row[name]) - set("01xz"):
                raise ValueError(f"cycle {cycle}: bad {width}-bit value for {name}: {row[name]}")
        if row["resetn"] != str(int(cycle >= 0)):
            raise ValueError(f"cycle {cycle}: unexpected reset value")
        rows.append(row)
    return rows


def compare(label: str, expected: list[dict[str, str]], actual: list[dict[str, str]]) -> None:
    for cycle, (left, right) in enumerate(zip(expected, actual, strict=True), -RESET_CYCLES):
        for name, value in left.items():
            if value != right[name]:
                raise ValueError(f"{label} cycle {cycle}: {name} expected={value} actual={right[name]}")


def check_program(rows: list[dict[str, str]]) -> None:
    retired = [row for row in rows if row["rvfi_valid"] == "1"]
    words = [f'{int(row["rvfi_insn"], 2):08x}' for row in retired]
    expected = ["00500093", "00700113", "002081b3", "10302023", "10002203",
                "00418463", "02a00313", "000f83b3", "00100073"]
    if words != expected or retired[-1]["rvfi_trap"] != "1":
        raise ValueError(f"unexpected retirements: {words}")
    if retired[3]["rvfi_mem_wmask"] != "1111" or retired[4]["rvfi_mem_rmask"] != "1111":
        raise ValueError("expected full-word store and load")
    if "x" not in retired[7]["rvfi_rd_wdata"]:
        raise ValueError("uninitialized register read lost its x bits")


def check_counters(rows: list[dict[str, str]]) -> None:
    # csrrs rd, csr, x0. Use the instruction to select the RVFI half and
    # counter. Only the two low-word reads have a nonzero value on this run.
    reads = {0xc0002473: ("mcycle", 0), 0xc80024f3: ("mcycle", 32),
             0xc0202573: ("minstret", 0), 0xc82025f3: ("minstret", 32)}
    retired = []
    for index, row in enumerate(rows):
        active = None
        if row["rvfi_valid"] == "1":
            word = int(row["rvfi_insn"], 2)
            retired.append(word)
            active = reads.get(word)
        for counter in ("mcycle", "minstret"):
            mask = data = 0
            if active and active[0] == counter:
                half = active[1]
                rd = int(row["rvfi_rd_wdata"], 2)
                if (half == 0) != (rd != 0):
                    raise ValueError(f"{counter}: unexpected counter half value {rd}")
                mask, data = 0xffffffff << half, rd << half
            for field, value in (("rmask", mask), ("rdata", data), ("wmask", 0), ("wdata", 0)):
                name = f"rvfi_csr_{counter}_{field}"
                if row[name] != f"{value:064b}":
                    raise ValueError(f"cycle {index-RESET_CYCLES}: wrong {name}")
    if retired != [*reads, 0x00100073] or rows[-1]["rvfi_trap"] != "1":
        raise ValueError(f"counter test ended without its four reads and ebreak: {retired}")


def case_lines(transcript: list[str], case: str) -> list[str]:
    return transcript[transcript.index("BEGIN " + case) + 1:transcript.index("END " + case)]


def check_pins() -> None:
    for path, digest in ((SOURCE, SOURCE_SHA256), (ENVELOPE, ENVELOPE_SHA256),
                         (TESTBENCH, TESTBENCH_SHA256), (TRANSCRIPT, TRANSCRIPT_SHA256)):
        if hashlib.sha256(path.read_bytes()).hexdigest() != digest:
            raise ValueError(f"pinned hash mismatch for {path.name}")


def trace_schema() -> tuple[dict[str, int], int]:
    inputs, outputs = port_widths()
    # clk is sampled at the rising edge. The trace retains the response
    # before that edge and the new response after the NBA updates.
    schema = {k: v for k, v in inputs.items() if k != "clk"} | outputs
    schema["sampled_rdata"] = inputs["mem_rdata"]
    return schema, len(outputs)


def compile_bench(work: Path) -> list[str]:
    versions = [run(["iverilog", "-V"], work).splitlines()[0],
                run(["xrun", "-version"], work).splitlines()[0]]
    if ICARUS_PIN not in versions[0] or XCELIUM_PIN not in versions[1]:
        raise ValueError(f"unexpected simulator versions: {versions}")
    print(*versions, sep="\n", flush=True)
    top = "tb_picorv32_rvfi_long"
    run(["iverilog", "-g2012", "-DRISCV_FORMAL", "-s", top, "-o", "bench", SOURCE, TESTBENCH], work)
    run(["xrun", "-elaborate", "-sv", "-q", "-define", "RISCV_FORMAL", "-top", top, SOURCE, TESTBENCH], work)
    return versions


def simulate(work: Path, args: list[str]) -> list[str]:
    records = []
    for command in (["vvp", "bench", *args], ["xrun", "-R", "-q", *args]):
        records.append([line for line in run(command, work).splitlines()
                        if line.startswith(("CYCLE ", "CONSOLE ", "END trap="))])
    for index, (a, b) in enumerate(zip(*records, strict=True)):
        if a != b:
            raise ValueError(f"simulators differ at record {index}\nIcarus {a}\nXcelium {b}")
    return records[0]


def replay(files: list[Path], counts: list[int], output_count: int) -> bool:
    run(["lake", "build", "Examples.«system-verilog».cores.picorv32.input_drive_core"], ROOT)
    result = run(["lake", "env", "lean", "--run", REPLAY, *files], ROOT, timeout=None).strip()
    if result == "load refusal: " + EXPECTED_LOAD_REFUSAL:
        print(f"canonical E: 0/{sum(counts)} samples; {result}")
        return False
    if result.splitlines() != [f"{n} samples, {output_count} outputs agree" for n in counts]:
        raise RuntimeError(f"unexpected canonical-E result\n{result}")
    print(f"canonical E: {sum(counts)}/{sum(counts)} samples, {output_count} outputs agree")
    return True


def main() -> None:
    check_pins()
    schema, output_count = trace_schema()
    transcript = TRANSCRIPT.read_text().splitlines()
    with tempfile.TemporaryDirectory(prefix="picorv32-input-") as tmp:
        work = Path(tmp)
        if compile_bench(work) != transcript[:2]:
            raise ValueError("simulator versions differ from the transcript")
        files = []
        counts = []
        for case, active in CASE_CYCLES.items():
            records = simulate(work, ["+counters"] if case == "counters" else [])
            lines = [line for line in records if line.startswith("CYCLE ")]
            live = parse_rows(lines, schema, active)
            saved = case_lines(transcript, case)
            reference = parse_rows(saved, schema, active)
            compare(case + " transcript", reference, live)
            if case == "program":
                check_program(live)
            else:
                check_counters(live)
                # Corrupt one observed read-mask bit in the pinned transcript.
                name = "rvfi_csr_mcycle_rmask"
                index = next(i for i, row in enumerate(reference) if "1" in row[name])
                corrupt = reference.copy()
                corrupt[index] = reference[index] | {name: reference[index][name][:-1] + "0"}
                try:
                    compare("negative control", corrupt, live)
                except ValueError as exc:
                    if not str(exc).startswith(f"negative control cycle {index-RESET_CYCLES}: {name} "):
                        raise
                    print(exc)
                else:
                    raise AssertionError("corrupted RVFI read mask passed")
            file = work / (case + ".rows")
            file.write_text("\n".join(saved) + "\n")
            files.append(file)
            counts.append(len(live))
            print(f"{case}: {RESET_CYCLES} reset + {active} post-reset samples, {output_count} simulator outputs agree")
        replay(files, counts, output_count)


if __name__ == "__main__":
    main()
