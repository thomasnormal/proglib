#!/usr/bin/env python3
"""Differential rows for the canonical-E parameterized FIFO fixture."""
from pathlib import Path
import os
import shutil
import signal
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [
    ["reset", "x" * 32, "1", "0", "000", "0", "0"],
    ["push0", f"{0xa5:032b}", "0", "0", "001", "1", "0"],
    ["push1", f"{0xa5:032b}", "0", "0", "010", "1", "0"],
    ["pop0", f"{0x5a:032b}", "0", "0", "001", "0", "1"],
    ["both", f"{0x3c:032b}", "0", "0", "001", "1", "1"],
    ["settled", f"{0x3c:032b}", "0", "0", "001", "0", "0"],
]


def run(args, cwd=ROOT):
    proc = subprocess.Popen(args, cwd=cwd, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, start_new_session=True)
    try:
        out, err = proc.communicate(timeout=120)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        out, err = proc.communicate()
        raise RuntimeError(f"{args[0]} timed out:\n{out}{err}")
    if proc.returncode:
        raise RuntimeError(f"{args[0]} exited {proc.returncode}:\n{out}{err}")
    return out, err


def rows(output):
    answer = []
    for line in output.splitlines():
        if not line.startswith("ROW "):
            continue
        fields = line.split()
        answer.append([fields[1]] + [field.split("=", 1)[1] for field in fields[2:]])
    return answer


def source_rows(simulator):
    sources = [str(HERE / "parameterized_fifo_canonical_e.sv"),
               str(HERE / "parameterized_fifo_canonical_e_tb.sv")]
    with tempfile.TemporaryDirectory(prefix="sv-e-parameterized-fifo-") as work:
        if simulator == "iverilog":
            exe = str(Path(work) / "sim")
            run(["iverilog", "-g2012", "-s", "parameterized_fifo_canonical_e_tb",
                 "-o", exe] + sources, work)
            output, _ = run(["vvp", exe], work)
        else:
            output, _ = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                             "-top", "parameterized_fifo_canonical_e_tb"] + sources, work)
    return rows(output)


def main():
    run(["lake", "env", "lean",
         "Examples/system-verilog/sem2/parameterized_fifo_canonical_e/agree.lean"])
    print("canonical E parameterized FIFO receipt: PASS")
    if not shutil.which("iverilog") or not shutil.which("vvp"):
        raise RuntimeError("Icarus is required for this differential check")
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
