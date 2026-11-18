#!/usr/bin/env python3
"""Check the system-function call row against canonical E and both simulators."""

from __future__ import annotations

from pathlib import Path
import shutil
import subprocess
import tempfile


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[5]
SOURCE = HERE / "function_call_expression_repro.sv"
TB = HERE / "function_call_expression_repro_tb.sv"
EXPECTED = {
    (): ["ROW in=0 y=0", "ROW in=1 y=0"],
    ("+flag",): ["ROW in=0 y=0", "ROW in=1 y=1"],
}


def run(command: list[str], cwd: Path) -> str:
    result = subprocess.run(
        command,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
        timeout=180,
    )
    if result.returncode:
        raise RuntimeError("command failed: %s\n%s" % (" ".join(command), result.stdout))
    return result.stdout


def rows(output: str) -> list[str]:
    return [line.strip() for line in output.splitlines() if line.startswith("ROW ")]


def main() -> int:
    run(["lake", "env", "lean", str(HERE / "probe.lean")], ROOT)
    print("canonical E: exact SysCall refusal, no environment-dependent value claimed")
    if shutil.which("iverilog") is None or shutil.which("vvp") is None:
        raise RuntimeError("Icarus Verilog 13.0 is required")
    if shutil.which("xrun") is None:
        raise RuntimeError("Xcelium 24.03-s004 is required")

    with tempfile.TemporaryDirectory(prefix="sv-function-call-") as work:
        directory = Path(work)
        executable = directory / "sim"
        run(["iverilog", "-g2012", "-s", "function_call_expression_repro_tb",
             "-o", str(executable), str(SOURCE), str(TB)], directory)
        for plusargs, expected in EXPECTED.items():
            actual = rows(run(["vvp", str(executable), *plusargs], directory))
            if actual != expected:
                raise RuntimeError("Icarus %s: %r" % (plusargs, actual))
    print("Icarus Verilog 13.0: 2 rows MATCH without +flag and 2 rows MATCH with +flag")

    with tempfile.TemporaryDirectory(prefix="sv-function-call-xcelium-") as work:
        directory = Path(work)
        for plusargs, expected in EXPECTED.items():
            actual = rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                               "-top", "function_call_expression_repro_tb",
                               str(SOURCE), str(TB), *plusargs], directory))
            if actual != expected:
                raise RuntimeError("Xcelium %s: %r" % (plusargs, actual))
    print("Xcelium 24.03-s004: 2 rows MATCH without +flag and 2 rows MATCH with +flag")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
