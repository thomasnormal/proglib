#!/usr/bin/env python3
"""Compare source-shaped part- and bit-select rows with both simulators."""
from pathlib import Path
import os
import shutil
import signal
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[4]
sys.path.insert(0, str(ROOT / "harness/sv"))
from xcelium_probe import probe_xcelium  # noqa: E402

EXPECTED = [
    ["xxxxxxxx", "x"],
    ["01011010", "1"],
    ["01011010", "1"],
    ["01111000", "0"],
    ["01111000", "0"],
    ["01111000", "x"],
    ["01111000", "x"],
]


def run(args, cwd=ROOT):
    process = subprocess.Popen(
        args,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        start_new_session=True,
    )
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
        if line.startswith("ROW "):
            fields = line.split()
            result.append([
                fields[1].split("=", 1)[1],
                fields[2].split("=", 1)[1],
            ])
    return result


def source_rows(simulator):
    sources = [str(HERE / "selects.sv"), str(HERE / "selects_tb.sv")]
    with tempfile.TemporaryDirectory(prefix="sv-darkriscv-selects-") as work:
        if simulator == "iverilog":
            executable = str(Path(work) / "sim")
            run(
                ["iverilog", "-g2012", "-s", "selects_tb", "-o", executable]
                + sources,
                work,
            )
            output = run(["vvp", executable], work)
        else:
            output = run(
                [
                    "xrun",
                    "-sv",
                    "-q",
                    "-timescale",
                    "1ns/1ps",
                    "-top",
                    "selects_tb",
                ]
                + sources,
                work,
            )
    return rows(output)


def main():
    run(["lake", "env", "lean", "Examples/system-verilog/cores/darkriscv/walls/selects_probe.lean"])
    print("canonical E select rows: PASS")
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
