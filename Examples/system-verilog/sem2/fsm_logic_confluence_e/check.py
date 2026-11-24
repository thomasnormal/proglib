#!/usr/bin/env python3
"""Differential rows for the clean-room finite-state NBA witness."""
from pathlib import Path
import os
import shutil
import signal
import subprocess
import tempfile
HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [["first", "x", "x"], ["reset", "0", "0"], ["start", "1", "0"],
            ["run", "0", "1"], ["done", "0", "0"], ["idle", "0", "0"]]
def run(args, cwd=ROOT):
    p = subprocess.Popen(args, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE, start_new_session=True)
    try:
        out, err = p.communicate(timeout=120)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)
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
    sources = [str(HERE / "fsm_logic_confluence_e.sv"), str(HERE / "fsm_logic_confluence_e_tb.sv")]
    with tempfile.TemporaryDirectory(prefix="sv-e-fsm-") as work:
        if simulator == "iverilog":
            exe = str(Path(work) / "sim")
            run(["iverilog", "-g2012", "-s", "fsm_logic_confluence_e_tb", "-o", exe] + sources, work)
            out, _ = run(["vvp", exe], work)
        else:
            out, _ = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "fsm_logic_confluence_e_tb"] + sources, work)
    return rows(out)
def main():
    run(["lake", "env", "lean", "Examples/system-verilog/sem2/fsm_logic_confluence_e/agree.lean"])
    for simulator in ["iverilog"] + (["xrun"] if shutil.which("xrun") else []):
        actual = source_rows(simulator)
        if actual != EXPECTED:
            raise RuntimeError(f"{simulator}: expected {EXPECTED}, got {actual}")
        print(f"{simulator}: {len(actual)} rows MATCH")
if __name__ == "__main__":
    main()
