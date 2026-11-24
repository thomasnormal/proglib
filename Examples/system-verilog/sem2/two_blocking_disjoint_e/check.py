#!/usr/bin/env python3
"""Differential rows for the disjoint blocking confluence witness."""
from pathlib import Path
import os
import shutil
import signal
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [["initial", "x", "x"], ["edge0", "0", "1"], ["edge1", "1", "0"]]


def run(args, cwd=ROOT):
    p = subprocess.Popen(args, cwd=cwd, text=True, stdout=subprocess.PIPE,
                         stderr=subprocess.PIPE, start_new_session=True)
    try:
        out, err = p.communicate(timeout=120)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        out, err = p.communicate()
        raise RuntimeError(f"{args[0]} timed out:\n{out}{err}")
    if p.returncode:
        raise RuntimeError(f"{args[0]} exited {p.returncode}:\n{out}{err}")
    return out, err


def rows(output):
    answer = []
    for line in output.splitlines():
        if line.startswith("ROW "):
            fields = line.split()
            answer.append([fields[1]] + [x.split("=", 1)[1] for x in fields[2:]])
    return answer


def source_rows(simulator):
    sources = [str(HERE / "two_blocking_disjoint_e.sv"),
               str(HERE / "two_blocking_disjoint_e_tb.sv")]
    with tempfile.TemporaryDirectory(prefix="sv-e-blocking-disjoint-") as work:
        if simulator == "iverilog":
            exe = str(Path(work) / "sim")
            run(["iverilog", "-g2012", "-s", "two_blocking_disjoint_e_tb",
                 "-o", exe] + sources, work)
            out, _ = run(["vvp", exe], work)
        else:
            out, _ = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                          "-top", "two_blocking_disjoint_e_tb"] + sources, work)
    return rows(out)


def main():
    run(["lake", "env", "lean",
         "Examples/system-verilog/sem2/two_blocking_disjoint_e/agree.lean"])
    print("two-process blocking guard receipt: PASS")
    if not shutil.which("iverilog") or not shutil.which("vvp"):
        raise RuntimeError("Icarus is required")
    version, err = run(["iverilog", "-V"])
    print((version + err).splitlines()[0])
    simulators = ["iverilog"]
    if shutil.which("xrun"):
        simulators.append("xrun")
    else:
        print("no Xcelium result: xrun unavailable")
    for simulator in simulators:
        actual = source_rows(simulator)
        if actual != EXPECTED:
            raise RuntimeError(f"{simulator}: expected {EXPECTED}, got {actual}")
        print(f"{simulator}: {len(actual)} rows MATCH")


if __name__ == "__main__":
    main()
