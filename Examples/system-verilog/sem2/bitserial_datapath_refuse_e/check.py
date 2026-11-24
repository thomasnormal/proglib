#!/usr/bin/env python3
from pathlib import Path
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SOURCE = HERE / "bitserial_datapath_refuse_e.sv"
ENVELOPE = HERE / (SOURCE.name + ".json")

def main():
    with tempfile.NamedTemporaryFile(suffix=".json") as fresh:
        result = subprocess.run([
            "python3", "extractors/sv/extract.py", "--top",
            "bitserial_datapath_refuse_e", "-o", fresh.name,
            str(SOURCE.relative_to(ROOT))], cwd=ROOT, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT, check=True)
        if fresh.read() != ENVELOPE.read_bytes():
            raise RuntimeError("checked-in envelope differs from Slang extraction")
    census = subprocess.run([
        "python3", "harness/sv/refusal_census.py", "ordinary", str(ENVELOPE)],
        cwd=ROOT, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, check=True).stdout
    if "InvalidSelectExpression" not in census:
        raise RuntimeError(census)
    print("ordinary E: SlangError:InvalidSelectExpression refusal")
    for simulator in ("iverilog", "xrun"):
        if simulator == "iverilog":
            command = ["iverilog", "-g2012", "-s", "bitserial_datapath_refuse_e",
                       str(SOURCE)]
        else:
            command = ["xrun", "-sv", "-q", "-top", "bitserial_datapath_refuse_e",
                       str(SOURCE)]
        with tempfile.TemporaryDirectory(prefix="sv-bitserial-refuse-") as directory:
            result = subprocess.run(command, cwd=directory, text=True,
                                    stdout=subprocess.PIPE,
                                    stderr=subprocess.STDOUT, timeout=180)
        if result.returncode == 0:
            raise RuntimeError(f"{simulator} unexpectedly accepted invalid select")
        version = ("Icarus Verilog 13.0" if simulator == "iverilog"
                   else "Xcelium 24.03-s004")
        print(f"{version}: source rejected at parser/elaboration")

if __name__ == "__main__":
    main()
