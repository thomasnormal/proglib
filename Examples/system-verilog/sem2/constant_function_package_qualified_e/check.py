#!/usr/bin/env python3
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
from xcelium_probe import probe_xcelium


def run(args, cwd=ROOT):
    process = subprocess.Popen(
        args, cwd=cwd, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.PIPE, start_new_session=True)
    try:
        out, err = process.communicate(timeout=180)
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        out, err = process.communicate()
        raise RuntimeError(f"{args[0]} timed out: {out}{err}")
    if process.returncode:
        raise RuntimeError(f"{args[0]} exited {process.returncode}: {out}{err}")
    return out


def rows(output):
    return [line.split()[1:] for line in output.splitlines()
            if line.startswith("ROW ")]


def main():
    source = HERE / "constant_function_package_qualified_e.sv"
    envelope = HERE / "constant_function_package_qualified_e.sv.json"
    regenerated = Path(tempfile.mktemp(prefix="sv-qualified-package-",
                                        suffix=".json"))
    try:
        run([
            sys.executable, str(ROOT / "extractors/sv/extract.py"),
            "--top", "constant_function_package_qualified_e",
            "--retain-proc-rewrites", "-o", str(regenerated),
            str(source.relative_to(ROOT)),
        ])
        if regenerated.read_bytes() != envelope.read_bytes():
            raise RuntimeError("committed envelope is stale; re-extract it")
        import json
        extracted = json.loads(envelope.read_text())
        if extracted.get("packages") != [
                "constant_function_package_qualified_e_pkg"]:
            raise RuntimeError(
                f"qualified package metadata: {extracted.get('packages')}")
    finally:
        regenerated.unlink(missing_ok=True)

    refusal = subprocess.run(
        ["lake", "env", "lean", str(HERE / "oracle.lean")], cwd=ROOT,
        text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if refusal.returncode == 0 or "function 'vbits' in a constant context" not in refusal.stdout:
        raise RuntimeError(f"ordinary route refusal changed:\n{refusal.stdout}")
    print("E: REFUSED package function in constant context")

    tb = (
        "module tb; localparam integer N = `N; logic [7:0] y; "
        "constant_function_package_qualified_e #(.N(N)) dut(.y(y)); "
        "initial begin #1 $display(\"ROW N=%0d W=%0d y=%0d\", N, dut.W, y); "
        "$finish; end endmodule"
    )
    if shutil.which("iverilog"):
        actual = []
        for n in (1, 8, 16):
            with tempfile.TemporaryDirectory(prefix="sv-qualified-package-") as work:
                work_path = Path(work)
                testbench = work_path / "tb.sv"
                testbench.write_text(f"`define N {n}\n" + tb)
                executable = work_path / "sim"
                run([
                    "iverilog", "-g2012", "-s", "tb", "-o", str(executable),
                    str(source), str(testbench),
                ], work)
                actual.extend(rows(run(["vvp", str(executable)], work)))
        if actual != [["N=1", "W=1", "y=1"],
                      ["N=8", "W=3", "y=3"],
                      ["N=16", "W=4", "y=4"]]:
            raise RuntimeError(f"Icarus Verilog 13.0: {actual}")
        print("Icarus Verilog 13.0: 3 rows MATCH E")

    if shutil.which("xrun"):
        status, details = probe_xcelium()
        print(details)
        if status == 0:
            actual = []
            for n in (1, 8, 16):
                with tempfile.TemporaryDirectory(prefix="sv-qualified-package-") as work:
                    testbench = Path(work) / "tb.sv"
                    testbench.write_text("`define N %d\n" % n + tb)
                    actual.extend(rows(run([
                        "xrun", "-sv", "-q", "-define", f"N={n}",
                        "-top", "tb", str(source), str(testbench),
                    ], work)))
            if actual != [["N=1", "W=1", "y=1"],
                          ["N=8", "W=3", "y=3"],
                          ["N=16", "W=4", "y=4"]]:
                raise RuntimeError(f"Xcelium 24.03-s004: {actual}")
            print("Xcelium 24.03-s004: 3 rows MATCH E")
        elif status == 77:
            print("no Xcelium result: explicit license refusal")
        else:
            raise RuntimeError("Xcelium readiness failed")


if __name__ == "__main__":
    main()
