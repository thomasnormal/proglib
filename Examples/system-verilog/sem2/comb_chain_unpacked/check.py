#!/usr/bin/env python3
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
EXPECTED = [
    "ROW q=fc s0=fc s1=7e s2=3f",
    "ROW q=fc s0=fc s1=7e s2=3f",
    "ROW q=fc s0=fc s1=7e s2=3f",
    "ROW q=3f s0=3f s1=1f s2=0f",
]

def run(command, cwd=ROOT):
    result = subprocess.run(command, cwd=cwd, text=True,
                            stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=120)
    if result.returncode:
        raise RuntimeError(result.stdout)
    return result.stdout

def rows(output):
    return [line for line in output.splitlines() if line.startswith("ROW ")]

def main():
    with tempfile.TemporaryDirectory(prefix="sv-comb-chain-") as work:
        envelope = Path(work) / "envelope.json"
        run(["python3", "extractors/sv/extract.py", "--retain-proc-rewrites",
             "--top", "comb_chain_unpacked", "-o", str(envelope),
             str((HERE / "comb_chain_unpacked.sv").relative_to(ROOT))])
        if envelope.read_bytes() != (HERE / "comb_chain_unpacked.sv.json").read_bytes():
            raise RuntimeError("stale envelope")
        executable = Path(work) / "sim"
        run(["iverilog", "-g2012", "-s", "comb_chain_unpacked_tb",
             "-o", str(executable), str(HERE / "comb_chain_unpacked.sv"),
             str(HERE / "comb_chain_unpacked_tb.sv")], work)
        got = rows(run([str(executable)], work))
        if got != EXPECTED:
            raise RuntimeError(f"Icarus rows {got} != {EXPECTED}")
    print("Icarus Verilog 13.0: 4 rows MATCH")
    if shutil.which("xrun"):
        with tempfile.TemporaryDirectory(prefix="sv-xcelium-comb-chain-") as work:
            output = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                          "-top", "comb_chain_unpacked_tb",
                          str(HERE / "comb_chain_unpacked.sv"),
                          str(HERE / "comb_chain_unpacked_tb.sv")], work)
        got = rows(output)
        if got != EXPECTED:
            raise RuntimeError(f"Xcelium rows {got} != {EXPECTED}")
        print("Xcelium 24.03-s004: 4 rows MATCH")
    else:
        print("Xcelium 24.03-s004: unavailable")
    print("ordinary E: source-shaped genvar chain admitted")

if __name__ == "__main__":
    main()
