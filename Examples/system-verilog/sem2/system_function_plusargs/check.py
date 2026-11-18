#!/usr/bin/env python3
"""Measure $test$plusargs with the two pinned simulators."""
from pathlib import Path
import os
import shutil
import signal
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
sys.path.insert(0, str(ROOT / "harness/sv"))
from xcelium_probe import probe_xcelium  # noqa: E402

EXPECTED = {
    "none": [
        ["zero", "0", "0", "0"],
        ["one", "0", "1", "0"],
        ["x", "0", "x", "0"],
        ["z", "0", "z", "0"],
    ],
    "flag": [
        ["zero", "1", "0", "0"],
        ["one", "1", "1", "1"],
        ["x", "1", "x", "x"],
        ["z", "1", "z", "z"],
    ],
}


def run(args, cwd):
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
    return out


def rows(output):
    result = []
    for line in output.splitlines():
        if line.startswith("ROW "):
            fields = line.split()
            result.append([fields[1]] + [x.split("=", 1)[1] for x in fields[2:]])
    return result


def source_rows(tool, plusarg):
    sources = [str(HERE / "system_function_plusargs.sv"),
               str(HERE / "system_function_plusargs_tb.sv")]
    with tempfile.TemporaryDirectory(prefix="sv-system-function-plusargs-") as work:
        flag = ["+flag"] if plusarg else []
        if tool == "iverilog":
            exe = str(Path(work) / "sim")
            run(["iverilog", "-g2012", "-s", "system_function_plusargs_tb",
                 "-o", exe] + sources, work)
            return rows(run(["vvp", exe] + flag, work))
        return rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                         "-top", "system_function_plusargs_tb"] + sources + flag, work))


def main():
    if not shutil.which("iverilog") or not shutil.which("vvp"):
        raise RuntimeError("Icarus is required")
    print(run(["iverilog", "-V"], ROOT).splitlines()[0])
    tools = ["iverilog"]
    if shutil.which("xrun"):
        status, details = probe_xcelium()
        print(details)
        if status == 0:
            print(run(["xrun", "-version"], ROOT).strip())
            tools.append("xrun")
        elif status == 77:
            print("no Xcelium result: explicit license refusal")
        else:
            raise RuntimeError("Xcelium readiness probe failed")
    else:
        print("no Xcelium result: xrun unavailable")
    for tool in tools:
        for mode, plusarg in (("none", False), ("flag", True)):
            actual = source_rows(tool, plusarg)
            if actual != EXPECTED[mode]:
                raise RuntimeError(f"{tool} {mode}: expected {EXPECTED[mode]}, got {actual}")
            print(f"{tool} {mode}: {len(actual)} rows MATCH source")


if __name__ == "__main__":
    main()
