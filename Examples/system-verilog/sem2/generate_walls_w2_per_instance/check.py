#!/usr/bin/env python3
"""Differential rows for the W2 per-instance generate declaration packet."""
from pathlib import Path
import shutil
import subprocess
import tempfile

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
CASES = [
    ("w2a_gfor_scalar", "m", "q", "", ["00", "01", "10", "xz"]),
    ("w2b_gfor_vector", "m", "q", "", ["00", "01", "10", "xz"]),
    ("w2c_gfor_unpacked", "m", "q", "", ["00", "01", "10", "xz"]),
    ("w2e_two_loops_same_name", "m", "q", "p", ["0", "1", "x", "z"]),
    ("w2f_shadow_module_name", "m", "q", "z", ["0", "1", "x", "z"]),
    ("w2h_gfor_no_decl", "m", "q", "", ["00", "01", "10", "xz"]),
]


def run(command, cwd=ROOT):
    result = subprocess.run(command, cwd=cwd, text=True,
                            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
                            timeout=180)
    if result.returncode:
        raise RuntimeError(result.stdout)
    return result.stdout


def rows(output):
    return [line for line in output.splitlines() if line.startswith("ROW ")]


def expected(case):
    name, _, out, other, inputs = case
    result = []
    for value in inputs:
        inv = "".join({"0": "1", "1": "0", "x": "x", "z": "x"}[bit] for bit in value)
        if name == "w2e_two_loops_same_name":
            result.append(f"ROW {name} {value} {value} {inv}")
        elif name == "w2f_shadow_module_name":
            result.append(f"ROW {name} {value} {inv} {value}")
        else:
            result.append(f"ROW {name} {value} {inv}")
    return result


def testbench(case):
    name, module, out, other, inputs = case
    width = 1 if len(inputs[0]) == 1 else 2
    ports = f".a(a), .{out}({out})"
    if other:
        ports += f", .{other}({other})"
    displays = f'$display("ROW {name} %b %b'
    if other:
        displays += " %b"
    displays += f'", a, {out}'
    if other:
        displays += f", {other}"
    displays += ");"
    assigns = "\n".join(f"    a = {width}'b{value}; #1; {displays}" for value in inputs)
    declarations = f"logic [{width - 1}:0] a; wire [{width - 1}:0] {out};"
    if other:
        declarations += f" wire [{width - 1}:0] {other};"
    return f'''module tb;
  {declarations}
  {module} #(.N({width})) dut({ports});
  initial begin
{assigns}
    $finish;
  end
endmodule
'''


def main():
    scratch = ROOT / ".scratch"
    scratch.mkdir(exist_ok=True)
    for name, _, _, _, _ in CASES:
        source = HERE / f"{name}.sv"
        envelope = HERE / f"{name}.json"
        with tempfile.NamedTemporaryFile(dir=scratch, suffix=".json") as fresh:
            run(["python3", "extractors/sv/extract.py", "--top", "m",
                 "-o", fresh.name, str(source.relative_to(ROOT))])
            if Path(fresh.name).read_bytes() != envelope.read_bytes():
                raise RuntimeError(f"{name}: checked-in envelope differs from Slang extraction")
    run(["lake", "env", "lean", str(HERE / "agree.lean")])
    simulators = ["iverilog"]
    if shutil.which("xrun"):
        simulators.append("xrun")
    for simulator in simulators:
        for case in CASES:
            name, _, _, _, _ = case
            source = HERE / f"{name}.sv"
            with tempfile.TemporaryDirectory(dir=scratch, prefix=f"sv-{name}-") as work:
                work_path = Path(work)
                tb = work_path / "tb.sv"
                tb.write_text(testbench(case))
                if simulator == "iverilog":
                    executable = work_path / "sim"
                    run(["iverilog", "-g2012", "-s", "tb", "-o", str(executable),
                         str(source), str(tb)], work)
                    output = run(["vvp", str(executable)], work)
                else:
                    output = run(["xrun", "-sv", "-q", "-timescale", "1ns/1ps",
                                  "-top", "tb", str(source), str(tb)], work)
            actual = rows(output)
            want = expected(case)
            if actual != want:
                raise RuntimeError(f"{simulator} {name}: {actual!r} != {want!r}")
            print(f"{simulator} {name}: {len(actual)} rows MATCH")


if __name__ == "__main__":
    main()
