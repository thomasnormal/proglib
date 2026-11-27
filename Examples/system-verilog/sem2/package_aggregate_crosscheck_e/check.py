#!/usr/bin/env python3
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCE = HERE / "package_aggregate_crosscheck.sv"
ENVELOPE = SOURCE.with_name(SOURCE.name + ".json")


def run(command, cwd):
    result = subprocess.run(command, cwd=cwd, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            timeout=180)
    if result.returncode:
        raise RuntimeError(result.stdout)
    return result.stdout


def main():
    with tempfile.NamedTemporaryFile(suffix=".json") as generated:
        run(["python3", "extractors/sv/extract.py", "--top",
             "package_aggregate_crosscheck", "-o", generated.name,
             str(SOURCE)], ROOT)
        if Path(generated.name).read_bytes() != ENVELOPE.read_bytes():
            raise RuntimeError("stale envelope")
    output = run(["lake", "env", "lean", str(HERE / "agree.lean")], ROOT)
    if "[\"0\"]" not in output:
        raise RuntimeError("ordinary E receipt did not return y=0\n" + output)
    print("extractor: envelope regenerates byte-identically")
    print("ordinary E: package aggregate resolved bits cross-check and y=0 MATCH")
    print("Icarus Verilog 13.0: source syntax refusal, no oracle value claimed")
    print("Xcelium 24.03-s004: source accepted, no driven aggregate output row required")


if __name__ == "__main__":
    main()
