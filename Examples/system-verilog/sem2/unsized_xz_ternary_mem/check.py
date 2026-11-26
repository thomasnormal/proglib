#!/usr/bin/env python3
"""Compare the unsized x/z ternary and dynamic-memory rows with both simulators."""
from pathlib import Path
import os
import shutil
import signal
import subprocess
import tempfile
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
sys.path.insert(0, str(ROOT / "harness/sv"))
from xcelium_probe import probe_xcelium  # noqa: E402

EXPECTED = [
    ["a0", "00000000", "xxxxxxxx"],
    ["a1", "zzzz0001", "xxxxxxxx"],
    ["ax", "xxxx000x", "xxxxxxxx"],
    ["az", "xxxx000x", "xxxxxxxx"],
]


def run(args, cwd=ROOT):
    process = subprocess.Popen(
        args, cwd=cwd, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, start_new_session=True)
    try:
        stdout, stderr = process.communicate(timeout=120)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        stdout, stderr = process.communicate()
        raise RuntimeError(f"{args[0]} timed out:\n{stdout}{stderr}")
    if process.returncode:
        raise RuntimeError(f"{args[0]} exited {process.returncode}:\n{stdout}{stderr}")
    return stdout


def rows(output):
    result = []
    for line in output.splitlines():
        if not line.startswith("ROW "):
            continue
        fields = line.split()
        result.append([fields[1]] + [field.split("=", 1)[1] for field in fields[2:]])
    return result


def source_rows(simulator):
    sources = [
        str(HERE / "unsized_xz_ternary_mem.sv"),
        str(HERE / "unsized_xz_ternary_mem_tb.sv"),
    ]
    with tempfile.TemporaryDirectory(prefix="sv-unsized-xz-ternary-mem-") as work:
        if simulator == "iverilog":
            executable = str(Path(work) / "sim")
            run(["iverilog", "-g2012", "-s", "unsized_xz_ternary_mem_tb",
                 "-o", executable] + sources, work)
            output = run(["vvp", executable], work)
        else:
            output = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                          "-top", "unsized_xz_ternary_mem_tb"] + sources, work)
    return rows(output)


def main():
    run(["lake", "env", "lean",
         "Examples/system-verilog/sem2/unsized_xz_ternary_mem/agree.lean"])
    print("canonical E unsized x/z and memory guards: PASS")
    if not shutil.which("iverilog") or not shutil.which("vvp"):
        raise RuntimeError("Icarus is required for this differential check")
    print(run(["iverilog", "-V"]).splitlines()[0])
    simulators = ["iverilog"]
    if shutil.which("xrun"):
        status, details = probe_xcelium()
        print(details)
        if status == 0:
            print(run(["xrun", "-version"]).strip())
            simulators.append("xrun")
        elif status == 77:
            print("no Xcelium result: explicit license refusal")
        else:
            raise RuntimeError("Xcelium readiness probe failed")
    else:
        print("no Xcelium result: xrun unavailable")
    for simulator in simulators:
        actual = source_rows(simulator)
        if actual != EXPECTED:
            raise RuntimeError(f"{simulator}: expected {EXPECTED}, got {actual}")
        print(f"{simulator}: {len(actual)} rows MATCH E")


if __name__ == "__main__":
    main()
