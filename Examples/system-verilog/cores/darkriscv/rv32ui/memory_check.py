#!/usr/bin/env python3
"""Build pinned RV32UI images and compare their execution on DarkRISCV."""
from __future__ import annotations

import argparse
from dataclasses import dataclass
import gzip
import hashlib
import os
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
RTL = HERE.parent / "rtl"
PIN = "3df703cd52d5f0d8224e3c50bf03c6cb70efff98"
ENV_PIN = "6de71edb142be36319e380ce782c3d1830c65d68"
PROGRAMS = (HERE / "programs.txt").read_text().splitlines()
TRANSCRIPT = HERE / "memory_rows.txt.gz"


def run(*args: str | Path, cwd: Path, timeout: int = 900) -> str:
    result = subprocess.run(args, cwd=cwd, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=timeout)
    if result.returncode:
        raise RuntimeError(f"{args[0]} exited {result.returncode}:\n{result.stdout[-4000:]}")
    return result.stdout


def write_hex(path: Path, blob: bytes | bytearray) -> None:
    words = (int.from_bytes(blob[i:i + 4], "little") for i in range(0, len(blob), 4))
    path.write_text("".join(f"{word:08x}\n" for word in words))


def build_image(src: Path, program: str, work: Path) -> tuple[str, int, int | None]:
    run("clang", "--target=riscv32", "-march=rv32i", "-mabi=ilp32", "-c",
        "-I", "isa/macros/scalar", "-I", "env/p", f"isa/rv32ui/{program}",
        "-o", work / "image.o", cwd=src)
    run("ld.lld", "-m", "elf32lriscv", "-Ttext=0", "--image-base=0", "image.o",
        "-o", "image.elf", cwd=work)
    run("objcopy", "-I", "elf32-little", "-O", "binary", "image.elf", "image.bin", cwd=work)
    blob = (work / "image.bin").read_bytes()
    if len(blob) > 16384:
        raise ValueError(f"{program}: image exceeds the test RAM")
    write_hex(work / "image.hex", blob)

    symbols = {}
    for line in run("nm", "-n", "image.elf", cwd=work).splitlines():
        fields = line.split()
        if len(fields) == 3:
            symbols[fields[2]] = int(fields[0], 16)
    if program == "simple.S":
        # The pinned simple test consists of RVTEST_PASS directly after the
        # reset prologue. Its linked image has no named pass or fail symbol.
        pass_pc, fail_pc = 0x194, None
    else:
        pass_pc, fail_pc = symbols["pass"], symbols["fail"]
    if int.from_bytes(blob[pass_pc:pass_pc + 4], "little") != 0x0ff0000f:
        raise ValueError(f"{program}: expected the fence starting RVTEST_PASS")
    return hashlib.sha256(blob).hexdigest(), pass_pc, fail_pc


def records(output: str) -> list[str]:
    return [line for line in output.splitlines() if line.startswith(("ROW ", "END "))]


def simulator_records(sim: Path) -> list[str]:
    arg = "+image=image.hex"
    iv = records(run("vvp", "memory.vvp", arg, cwd=sim))
    xc = records(run("xrun", "-R", "-q", arg, cwd=sim))
    if iv != xc:
        first = next((i for i, pair in enumerate(zip(iv, xc)) if pair[0] != pair[1]),
                     min(len(iv), len(xc)))
        raise ValueError(f"simulators differ at record {first}")
    return iv


COLUMNS = ("cycle RES IDATA IDACK DATAI DDACK IDREQ IADDR DDREQ DADDR DLEN DBE DRW DRD DWR "
           "DATAO DEBUG ESIMACK XRES HLT FLUSH PC XIDATA IERR gp a0 a7").split()


@dataclass(frozen=True)
class Outcome:
    path: str
    pc: int
    exit_regs: tuple[int, int, int] | None

    def describe(self) -> str:
        if self.exit_regs is None:
            return f"{self.path}, re-entered reset vector"
        gp, a0, a7 = self.exit_regs
        return f"{self.path}, ecall at {self.pc:#x}, gp={gp} a0={a0} a7={a7}"


def validate(program: str, lines: list[str], pass_pc: int, fail_pc: int | None) -> Outcome:
    if len(lines) < 6 or lines[-1] not in {"END ecall", "END restarted"}:
        raise ValueError(f"{program}: no terminal observation")
    starts = 0
    path = "neither label"
    for cycle, line in enumerate(lines[:-1]):
        tag, *fields = line.split()
        row = dict(zip(COLUMNS, fields, strict=True))
        if tag != "ROW" or row["cycle"] != str(cycle) or row["RES"] != str(int(cycle < 4)):
            raise ValueError(f"{program}: malformed cycle {cycle}")
        if (row["RES"], row["XRES"], row["HLT"], row["FLUSH"]) != ("0", "0", "0", "00"):
            continue
        pc = int(row["PC"], 2)
        if pc == pass_pc:
            if int(row["XIDATA"], 2) != 0x0ff0000f:
                raise ValueError(f"{program}: wrong instruction at RVTEST_PASS")
            path = "pass label"
        elif pc == fail_pc:
            path = "fail label"
        starts += int(pc == 0)
        if starts == 2:
            terminal = "restarted"
        elif int(row["XIDATA"], 2) == 0x73:
            terminal = "ecall"
        else:
            continue
        if cycle != len(lines) - 2 or lines[-1] != f"END {terminal}":
            raise ValueError(f"{program}: wrong terminal row at cycle {cycle}")
        if terminal == "ecall":
            gp, a0, a7 = (int(row[name], 2) for name in ("gp", "a0", "a7"))
            return Outcome(path, pc, (gp, a0, a7))
        return Outcome(path, pc, None)
    raise ValueError(f"{program}: terminal marker without an executing instruction")


def check(src: Path, work: Path, programs: list[str], record_to: Path | None) -> None:
    for repo, revision in ((src, PIN), (src / "env", ENV_PIN)):
        if (run("git", "rev-parse", "HEAD", cwd=repo).strip() != revision
                or run("git", "status", "--porcelain", cwd=repo).strip()):
            raise ValueError(f"expected clean pinned checkout at {repo}")
    if sorted(p.name for p in (src / "isa/rv32ui").glob("*.S")) != sorted(PROGRAMS):
        raise ValueError("programs.txt differs from the pinned rv32ui assembly corpus")
    for path, pin in ((RTL / "config.vh", "5871d964cbd6fc050680776e840026b80863616834dabdb55e78245d46b8566e"),
                      (RTL / "darkriscv.v", "46d57b15cc42c0458e02500a2a30371cd4e7979970c27afd9d47c40d1fa8c1a0"),
                      (HERE.parent / "darkriscv.sv.json", "ca7ba5a2e87ea6a1c2c0eb6b4975ac1a5c1787999241c4ba777adb25de82cd32")):
        if hashlib.sha256(path.read_bytes()).hexdigest() != pin:
            raise ValueError(f"pin differs: {path.name}")
    header = [f"riscv-tests {PIN} env {ENV_PIN}"]
    for tool, flag, pin in (("clang", "--version", "21.1.8"), ("ld.lld", "--version", "21.1.8"),
                            ("iverilog", "-V", "s20250103-64-gdad78d525"), ("xrun", "-version", "24.03-s004")):
        version = run(tool, flag, cwd=work).splitlines()[0]
        if pin not in version:
            raise ValueError(f"unexpected {tool} version: {version}")
        header.append(version)
        print(version, flush=True)

    # The RTL includes ../rtl/config.vh relative to the simulator's workdir.
    sim = work / "sim"
    sim.mkdir()
    (work / "rtl").symlink_to(RTL, target_is_directory=True)
    bench = HERE / "memory_tb.sv"
    run("iverilog", "-g2012", "-DSIMULATION", "-I../rtl", "-s", "rv32ui_memory_tb",
        "-o", "memory.vvp", bench, RTL / "darkriscv.v", cwd=sim)
    run("xrun", "-elaborate", "-sv", "-q", "-define", "SIMULATION", "-I../rtl",
        "-top", "rv32ui_memory_tb", bench, RTL / "darkriscv.v", cwd=sim)
    reference = {}
    if record_to is None:
        with gzip.open(TRANSCRIPT, "rt") as stream:
            stored = stream.read().split("BEGIN ")
        if stored[0].splitlines() != header:
            raise ValueError("transcript toolchain header differs")
        for block in stored[1:]:
            reference[block.split()[0]] = block
    blocks = []
    files = []
    outcomes = []
    cycles = 0
    for program in programs:
        image_hash, pass_pc, fail_pc = build_image(src, program, sim)
        iv = simulator_records(sim)
        outcome = validate(program, iv, pass_pc, fail_pc)
        outcomes.append(outcome)
        cycles += len(iv) - 1
        block = f"{program} image-sha256={image_hash} {outcome.describe()}\n" + "\n".join(iv) + "\n"
        if record_to is None and reference.get(program) != block:
            raise ValueError(f"{program}: live transcript differs from the pin")
        blocks.append(block)
        path = work / f"{program}.rows"
        path.write_text("\n".join(iv[:-1]) + "\n")
        files.append(path)
        print(f"{program}: {len(iv)-1} simulator cycles, {outcome.describe()}", flush=True)
        if program == "lb.S":
            # The first byte-load check expects 0xff at the linked tdat symbol.
            # Flip just that byte's low bit in the temporary RAM image.
            symbols = run("nm", "-n", "image.elf", cwd=sim).splitlines()
            tdat = next(int(line.split()[0], 16) for line in symbols if line.endswith(" tdat"))
            data = bytearray((sim / "image.bin").read_bytes())
            if data[tdat] != 0xff:
                raise ValueError("lb.S: unexpected value at tdat")
            data[tdat] ^= 1
            write_hex(sim / "image.hex", data)
            fault = simulator_records(sim)
            if validate(program, fault, pass_pc, fail_pc).path != "fail label":
                raise ValueError("lb.S accepted the corrupted test byte")
            (work / "lb-corrupted-data.rows").write_text("\n".join(fault[:-1]) + "\n")
    run("lake", "build", "darkriscv-replay", cwd=ROOT)
    lean = [ROOT / ".lake/build/bin/darkriscv-replay"]
    replay_files = list(files)
    if "lb.S" in programs:
        replay_files.append(work / "lb-corrupted-data.rows")
    print(run(*lean, *replay_files, cwd=ROOT, timeout=7200).strip(), flush=True)

    # Flip a bit of a sampled output, leaving the stimulus untouched.
    lines = files[0].read_text().splitlines()
    fields = lines[-1].split()
    fields[7] = "0" if fields[7] == "1" else "1"
    lines[-1] = " ".join(fields)
    wrong = work / "corrupted.rows"
    wrong.write_text("\n".join(lines) + "\n")
    try:
        run(*lean, wrong, cwd=ROOT)
    except RuntimeError as error:
        if f":{len(lines)-1}: IDREQ E=" not in str(error):
            raise
    else:
        raise AssertionError("Lean accepted the corrupted IDREQ output")
    print("corrupted IDREQ rejected", flush=True)
    reached_pass = sum(o.path == "pass label" for o in outcomes)
    exit_pass = sum(o.path == "pass label" and o.exit_regs == (1, 0, 93) for o in outcomes)
    print(f"{len(files)} three-way images, {cycles} cycles; "
          f"{reached_pass} reached RVTEST_PASS, {exit_pass} issued its expected exit arguments")
    if record_to is not None:
        data = "\n".join(header) + "\n" + "".join("BEGIN " + b for b in blocks)
        compressed = gzip.compress(data.encode(), mtime=0)
        with tempfile.NamedTemporaryFile(dir=record_to.parent, delete=False) as output:
            temporary = Path(output.name)
        try:
            temporary.write_bytes(compressed)
            temporary.replace(record_to)
        finally:
            temporary.unlink(missing_ok=True)


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("checkout", type=Path, help="pinned riscv-tests with env submodule")
    parser.add_argument("program", nargs="*", help="optional program names from programs.txt")
    parser.add_argument("--record", type=Path, help="write the verified complete corpus to this file")
    args = parser.parse_args()
    if any(p not in PROGRAMS for p in args.program):
        parser.error("unknown program; see programs.txt")
    if args.program and args.record:
        parser.error("--record requires the whole corpus")
    with tempfile.TemporaryDirectory(prefix="rv32ui-memory-", dir=os.environ.get("TMPDIR")) as tmp:
        check(args.checkout.resolve(), Path(tmp), args.program or PROGRAMS, args.record)


if __name__ == "__main__":
    main()
