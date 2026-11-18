#!/usr/bin/env python3
"""Differential receipt for the generated invalid-assignment chain."""
from pathlib import Path
import os
import shutil
import signal
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [["1111"], ["x111"]]


def run(args, cwd=ROOT, timeout=240):
    proc = subprocess.Popen(args, cwd=cwd, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.PIPE, start_new_session=True)
    try:
        out, err = proc.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(proc.pid, signal.SIGKILL)
        out, err = proc.communicate()
        raise RuntimeError(f"{args[0]} timed out:\n{out}{err}")
    if proc.returncode:
        raise RuntimeError(f"{args[0]} exited {proc.returncode}:\n{out}{err}")
    return out


def rows(output):
    return [line.split()[1:] for line in output.splitlines()
            if line.startswith("ROW ")]


def main():
    generated = HERE / "invalid_chain2_wall.sv.json"
    with tempfile.NamedTemporaryFile(suffix=".json") as temp:
        run(["python3", "extractors/sv/extract.py", "--top",
             "invalid_chain2_wall", "-o", temp.name,
             str((HERE / "invalid_chain2_wall.sv").relative_to(ROOT))])
        if Path(temp.name).read_bytes() != generated.read_bytes():
            raise RuntimeError("extractor envelope is not reproducible")
    print("extractor: invalid-chain envelope regenerates byte-identically")

    run(["lake", "env", "lean",
         "Examples/system-verilog/sem2/invalid_chain2_wall/agree.lean"])
    print("E: retained invalid-chain nodes and loud generate-scope refusal")

    source = str(HERE / "invalid_chain2_wall.sv")
    tb = str(HERE / "invalid_chain2_wall_tb.sv")
    simulators = ["iverilog"] + (["xrun"] if shutil.which("xrun") else [])
    for simulator in simulators:
        with tempfile.TemporaryDirectory(prefix="sv-invalid-chain-wall-") as work:
            if simulator == "iverilog":
                exe = str(Path(work) / "sim")
                run(["iverilog", "-g2012", "-s", "invalid_chain2_tb",
                     "-o", exe, source, tb], work)
                actual = rows(run(["vvp", exe], work))
            else:
                actual = rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                                   "-top", "invalid_chain2_tb", source, tb], work))
        if actual != EXPECTED:
            raise RuntimeError(f"{simulator}: {actual!r} != {EXPECTED!r}")
        version = run(["iverilog", "-V"] if simulator == "iverilog"
                      else ["xrun", "-version"]).splitlines()[0]
        print(f"{version}: 2 source rows MATCH")


if __name__ == "__main__":
    main()
