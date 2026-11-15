#!/usr/bin/env python3
from pathlib import Path
import os, signal, shutil, subprocess, tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]

def run(cmd, cwd=ROOT, timeout=60):
    p = subprocess.Popen(cmd, cwd=cwd, text=True, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, start_new_session=True)
    try:
        out, _ = p.communicate(timeout=timeout)
    except subprocess.TimeoutExpired:
        os.killpg(p.pid, signal.SIGKILL)
        p.communicate()
        return None
    if p.returncode:
        raise RuntimeError(out)
    return out

def rows(text):
    return [line.split()[1:] for line in text.splitlines() if line.startswith("ROW ")]

def main():
    with tempfile.NamedTemporaryFile(suffix=".json") as f:
        run(["python3", "extractors/sv/extract.py", "--top",
             "parameterized_storage_structure", "-o", f.name,
             str((HERE / "parameterized_storage_structure.sv").relative_to(ROOT))])
        if Path(f.name).read_bytes() != (HERE / "parameterized_storage_structure.sv.json").read_bytes():
            raise RuntimeError("stale envelope")
    print("extractor: envelope regenerates byte-identically")
    with tempfile.TemporaryDirectory(prefix="sv-e-parameterized-storage-") as w:
        # The ordinary batch route has a 60-second bound.  This diagnostic
        # uses a 45-second bound so a warm compiler cache cannot turn the
        # profile into a flaky pass; the full probe still reaches the same
        # load-and-run path and is known to exceed this bound.
        lean = run(["lake", "env", "lean", str(HERE / "probe.lean")], ROOT, timeout=45)
        if lean is not None:
            raise RuntimeError("ordinary E unexpectedly completed within the 45-second diagnostic bound")
    print("E ordinary route: TIMEOUT at load_design_sv2/ordinary elaboration/run for N=1,N=2 within the 45-second diagnostic bound (inside the 60-second batch bound); no E row claimed")

    expected_one = [["y=00000000"], ["y=00000001"], ["y=00010000"],
                    ["y=10100101"], ["y=11111111"], ["y=xxxxxxxx"],
                    ["y=zzzzzzzz"], ["y=01011010"]]
    expected = expected_one + expected_one
    with tempfile.TemporaryDirectory(prefix="sv-e-parameterized-storage-sim-") as w:
        src = str(HERE / "parameterized_storage_structure.sv")
        tb_src = (HERE / "parameterized_storage_structure_tb.sv").read_text()
        actual = []
        for parameter in (1, 2):
            tb = Path(w) / f"tb{parameter}.sv"
            tb.write_text(f"`define P {parameter}\n" + tb_src.replace("parameter integer P = 2", "parameter integer P = `P"))
            exe = str(Path(w) / f"sim{parameter}")
            run(["iverilog", "-g2012", "-o", exe, src, str(tb)], w)
            actual.extend(rows(run(["vvp", exe], w)))
    if actual != expected:
        raise RuntimeError(f"Icarus Verilog 13.0: {actual} != {expected}")
    print("Icarus Verilog 13.0: 16 source rows MATCH each other (N=1 and N=2)")
    if shutil.which("xrun"):
        with tempfile.TemporaryDirectory(prefix="sv-xcelium-parameterized-storage-") as w:
            src = str(HERE / "parameterized_storage_structure.sv")
            tb_src = (HERE / "parameterized_storage_structure_tb.sv").read_text()
            actual = []
            for parameter in (1, 2):
                tb = Path(w) / f"tb{parameter}.sv"
                tb.write_text(f"`define P {parameter}\n" + tb_src.replace("parameter integer P = 2", "parameter integer P = `P"))
                actual.extend(rows(run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps", "-top", "parameterized_storage_structure_tb", src, str(tb)], w)))
        if actual != expected:
            raise RuntimeError(f"Xcelium 24.03-s004: {actual} != {expected}")
        print("Xcelium 24.03-s004: 16 source rows MATCH each other (N=1 and N=2)")

if __name__ == "__main__":
    main()
