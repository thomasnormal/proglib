#!/usr/bin/env python3
"""Replay the RV32UI transcript, or rebuild and run the pinned tests with both simulators."""
from __future__ import annotations

import argparse
from contextlib import ExitStack
import gzip
import hashlib
import io
from pathlib import Path
import shutil
import tempfile
from typing import TextIO

import e_run_input_check as core

DATA = Path(__file__).resolve().parent / "rv32ui"
TRANSCRIPT = DATA / "simulator_rows.txt.gz"
PROGRAMS = DATA.parents[1] / "darkriscv/rv32ui/programs.txt"
SUITE = "3df703cd52d5f0d8224e3c50bf03c6cb70efff98"
PICO = "ef203c2b0a3fb793280f5114941416c425c5b461"
HEADER_SHA256 = "b345c17cda9e6980b7a075ad27c87d01be53802a99e7aa93941a4213e1bc1c43"
TRANSCRIPT_SHA256 = "5efbfd427b0040afd3a755b37cd67ffab4cd75046292f044ae0dbeb711372357"
EARLY_TRAPS = {"fence_i.S": 0x0000100f, "ma_data.S": 0x00141383}
FAULT = "lb-corrupt"
TOOLCHAIN = [("clang", "--version", "21.1.8"), ("ld.lld", "--version", "21.1.8")]


def programs() -> list[str]:
    return PROGRAMS.read_text().splitlines()


def symbols(work: Path) -> dict[str, int]:
    found = {}
    for line in core.run(["nm", "-n", "image.elf"], work).splitlines():
        fields = line.split()
        if len(fields) == 3:
            found[fields[2]] = int(fields[0], 16)
    return found


def build(src: Path, name: str, work: Path) -> tuple[str, int]:
    asm = "lb.S" if name == FAULT else name
    core.run(["clang", "--target=riscv32", "-march=rv32i", "-mabi=ilp32", "-I", DATA,
              "-I", src / "isa/macros/scalar", "-c", src / "isa/rv32ui" / asm, "-o", "image.o"], work)
    core.run(["ld.lld", "-m", "elf32lriscv", "-Ttext=0", "--image-base=0", "-e", "mytest",
              "image.o", "exit.o", "-o", "image.elf"], work)
    core.run(["objcopy", "-I", "elf32-little", "-O", "binary", "image.elf", "image.bin"], work)
    data = bytearray((work / "image.bin").read_bytes())
    labels = symbols(work)
    if len(data) > 16384 or labels["mytest"] != 0:
        raise ValueError(f"{name}: image does not fit at the reset vector")
    if name == FAULT:
        tdat = labels["tdat"]
        if data[tdat] != 0xff:
            raise ValueError("lb.S: unexpected first test byte")
        data[tdat] ^= 1
    (work / "image.hex").write_text("".join(f"{int.from_bytes(data[i:i+4], 'little'):08x}\n"
                                           for i in range(0, len(data), 4)))
    return hashlib.sha256(data).hexdigest(), labels["mytest_ret"]


def outcome(name: str, records: list[str], rows: list[dict[str, str]], ret_pc: int) -> str:
    if len(rows) <= core.RESET_CYCLES or records[-1:] != ["END trap=1"]:
        raise ValueError(f"{name}: empty or unfinished simulation")
    last = rows[-1]
    if last["trap"] != "1" or last["rvfi_valid"] != "1" or last["rvfi_trap"] != "1":
        raise ValueError(f"{name}: missing trapping retirement")
    console = bytes(int(s.split()[1], 16) for s in records if s.startswith("CONSOLE "))
    # The testbench observes acknowledged writes at the memory interface.
    # Independently reconstruct their bytes from the retired RVFI stores.
    stores = bytes(int(r["rvfi_mem_wdata"], 2) & 0xff for r in rows
                   if r["rvfi_valid"] == "1" and r["rvfi_mem_wmask"] == "1111"
                   and r["rvfi_mem_addr"] == f"{0x10000000:032b}")
    if console != stores:
        raise ValueError(f"{name}: RVFI stores differ from the console")
    pc, word = (int(last[key], 2) for key in ("rvfi_pc_rdata", "rvfi_insn"))
    if name in EARLY_TRAPS and console == b"mytest.." and word == EARLY_TRAPS[name]:
        return f"trapped at {pc:#x} on {word:#010x}"
    if name == FAULT and console == b"mytest..ERROR\n" and word == 0x00100073 and pc != ret_pc:
        return "upstream fail path"
    if (name not in EARLY_TRAPS and name != FAULT and console == b"mytest..OK\n"
            and pc == ret_pc and word == 0x00100073):
        return "upstream pass path"
    raise ValueError(f"{name}: console {console!r}, terminal PC {pc:#x}, instruction {word:#010x}")


def read_block(stream: TextIO, name: str) -> tuple[str, int, list[str]]:
    heading = stream.readline().split()
    if len(heading) != 4 or heading[:2] != ["IMAGE", name]:
        raise ValueError(f"missing transcript for {name}")
    records = []
    for line in stream:
        record = line.rstrip("\n")
        if not record.startswith(("CYCLE ", "CONSOLE ", "END ")):
            raise ValueError(f"{name}: invalid transcript record")
        records.append(record)
        if record.startswith("END "):
            return heading[2], int(heading[3], 16), records
    raise ValueError(f"{name}: truncated transcript")


def check(src: Path | None, record_to: Path | None, work: Path) -> bool:
    core.check_pins()
    schema, output_count = core.trace_schema()
    if hashlib.sha256((DATA / "riscv_test.h").read_bytes()).hexdigest() != HEADER_SHA256:
        raise ValueError("PicoRV32 test environment hash differs")
    progs = programs()
    versions = []
    if src is not None:
        if (core.run(["git", "rev-parse", "HEAD"], src).strip() != SUITE
                or core.run(["git", "status", "--porcelain"], src).strip()):
            raise ValueError("riscv-tests checkout must match the clean pin")
        if sorted(p.name for p in (src / "isa/rv32ui").glob("*.S")) != sorted(progs):
            raise ValueError("program inventory differs from upstream rv32ui")
        for tool, flag, pin in TOOLCHAIN:
            version = core.run([tool, flag], work).splitlines()[0]
            if pin not in version:
                raise ValueError(f"unexpected {tool} version: {version}")
            versions.append(version)
        versions += core.compile_bench(work)
        # The core's upstream header prints OK then jumps to mytest_ret.
        # Give the harness return address a trap instruction in its own object.
        (work / "exit.S").write_text(".text\n.global mytest_ret\nmytest_ret:\n    ebreak\n")
        core.run(["clang", "--target=riscv32", "-march=rv32i", "-mabi=ilp32", "-c", "exit.S", "-o", "exit.o"], work)

    ids = [f"riscv-tests {SUITE}", f"PicoRV32 {PICO}"]
    files, counts = [], []
    passes = 0
    packed = work / "verified.gz"
    with ExitStack() as stack:
        reader = writer = None
        if record_to is None:
            if hashlib.sha256(TRANSCRIPT.read_bytes()).hexdigest() != TRANSCRIPT_SHA256:
                raise ValueError("RV32UI transcript hash differs")
            reader = stack.enter_context(gzip.open(TRANSCRIPT, "rt"))
            saved = [reader.readline().rstrip("\n") for _ in range(6)]
            if saved[:2] != ids or (src is not None and saved[2:] != versions):
                raise ValueError("corpus or toolchain provenance differs")
            if src is None:
                print(*saved, sep="\n")
        else:
            raw = stack.enter_context(packed.open("wb"))
            zipped = stack.enter_context(gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0))
            writer = stack.enter_context(io.TextIOWrapper(zipped, encoding="utf-8"))
            writer.write("\n".join(ids + versions) + "\n")
        for name in [*progs, FAULT]:
            if reader is not None:
                digest, ret_pc, records = read_block(reader, name)
            if src is not None:
                built_hash, built_ret = build(src, name, work)
                live = core.simulate(work, ["+image=image.hex"])
                if reader is not None:
                    if (built_hash, built_ret) != (digest, ret_pc):
                        raise ValueError(f"{name}: linked image differs from the transcript")
                    for i, (a, b) in enumerate(zip(records, live, strict=True)):
                        if a != b:
                            raise ValueError(f"{name}: pinned record {i} differs\npin {a}\nlive {b}")
                digest, ret_pc, records = built_hash, built_ret, live
            lines = [r for r in records if r.startswith("CYCLE ")]
            rows = core.parse_rows(lines, schema, len(lines)-core.RESET_CYCLES)
            path = outcome(name, records, rows, ret_pc)
            passes += int(path == "upstream pass path")
            file = work / (name + ".rows")
            file.write_text("\n".join(lines) + "\n")
            files.append(file)
            counts.append(len(lines))
            if writer is not None:
                writer.write(f"IMAGE {name} {digest} {ret_pc:x}\n")
                writer.write("\n".join(records) + "\n")
            print(f"{name}: {len(rows)} samples, {path}", flush=True)
        if reader is not None and reader.read():
            raise ValueError("unexpected trailing transcript")
    print(f"{passes}/{len(progs)} images reached RVTEST_PASS; {sum(counts[:-1])} regular samples, "
          f"{counts[-1]} corrupted-image samples")
    agrees = core.replay(files, counts, output_count)
    if record_to is not None:
        with tempfile.NamedTemporaryFile(dir=record_to.parent, delete=False) as out:
            temporary = Path(out.name)
        try:
            shutil.copyfile(packed, temporary)
            temporary.replace(record_to)
        finally:
            temporary.unlink(missing_ok=True)
    print(f"E-RUN {len(progs) if agrees else 0}/{len(progs)} three-way images")
    return agrees


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", nargs="?", type=Path, help="clean pinned riscv-tests checkout for live comparison")
    parser.add_argument("--record", type=Path, help="write only the verified simulator transcript to this path")
    args = parser.parse_args()
    if args.record and args.checkout is None:
        parser.error("--record requires a live checkout")
    with tempfile.TemporaryDirectory(prefix="picorv32-rv32ui-") as tmp:
        agrees = check(args.checkout.resolve() if args.checkout else None, args.record, Path(tmp))
    raise SystemExit(0 if agrees else 2)


if __name__ == "__main__":
    main()
