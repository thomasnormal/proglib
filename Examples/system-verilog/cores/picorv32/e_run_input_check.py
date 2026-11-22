#!/usr/bin/env python3
"""Compare the loaded PicoRV32 against both simulators for 300 input cycles.

The testbench prints every observed output in bit form, retaining mixed
four-state values that hexadecimal formatting would hide.  The Lean side
replays the same reset and memory-input rows through the exact canonical-E
executor and compares every printed output field at every cycle.
"""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import subprocess
import tempfile


ROOT = Path(__file__).resolve().parents[4]
SOURCE = ROOT / "Examples/system-verilog/cores/picorv32/picorv32_r2.v"
ENVELOPE = ROOT / "Examples/system-verilog/cores/picorv32/picorv32_r2.sv.json"
TESTBENCH = ROOT / "Examples/system-verilog/cores/picorv32/rvfi_long_e_probe.v"
TRANSCRIPT = ROOT / "Examples/system-verilog/cores/picorv32/pico_simulator_transcript.txt"
EXPECTED_CYCLES = 300
SOURCE_SHA256 = "0836050971b3c6cdd28ac3b1e5719a67fb645161912bef1e472e63995ceb0622"
ENVELOPE_SHA256 = "17ea7b66ab8ea9b6844c317928f0430cff8b8a5b53f658f7a929bf1aa6cdc236"
TESTBENCH_SHA256 = "1dc356fbe89e36a5cd5e66006fdc32d9b7106f49f364c44ebcaa2b0ad42952fe"
TRANSCRIPT_SHA256 = "09380d29f5201a61f56e9101affb3d0e20ff6c601fae7a52bb33c65bb9875947"
EXPECTED_LOAD_REFUSAL = (
    "Schedule:preemptive: IEEE 1800-2023 §4.7 permits suspension between "
    "blocking writes; canonical E refuses a multi-write reactive process "
    "whose intermediate value another process can read"
)

INPUTS = {
    "resetn", "mem_ready", "mem_rdata", "pcpi_wr", "pcpi_rd",
    "pcpi_wait", "pcpi_ready", "irq",
}
WIDTHS = {
    "trap": 1, "mem_valid": 1, "mem_instr": 1, "mem_addr": 32,
    "mem_wdata": 32, "mem_wstrb": 4, "mem_la_read": 1,
    "mem_la_write": 1, "mem_la_addr": 32, "mem_la_wdata": 32,
    "mem_la_wstrb": 4, "rvfi_valid": 1, "rvfi_order": 64,
    "pcpi_valid": 1, "pcpi_insn": 32, "pcpi_rs1": 32, "pcpi_rs2": 32,
    "eoi": 32, "trace_valid": 1, "trace_data": 36,
    "rvfi_insn": 32, "rvfi_trap": 1, "rvfi_halt": 1, "rvfi_intr": 1,
    "rvfi_mode": 2, "rvfi_ixl": 2, "rvfi_rs1_addr": 5,
    "rvfi_rs1_rdata": 32, "rvfi_rs2_addr": 5, "rvfi_rs2_rdata": 32,
    "rvfi_rd_addr": 5, "rvfi_rd_wdata": 32, "rvfi_pc_rdata": 32,
    "rvfi_pc_wdata": 32, "rvfi_mem_addr": 32, "rvfi_mem_rmask": 4,
    "rvfi_mem_wmask": 4, "rvfi_mem_rdata": 32, "rvfi_mem_wdata": 32,
}


def run(command: list[str], cwd: Path, timeout: int = 900) -> str:
    result = subprocess.run(
        command, cwd=cwd, text=True, stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT, check=False, timeout=timeout,
    )
    if result.returncode:
        raise RuntimeError(
            "command failed (%d): %s\n%s"
            % (result.returncode, " ".join(command), result.stdout)
        )
    return result.stdout


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse_rows(output: str) -> list[dict[str, str]]:
    rows = [
        dict(re.findall(r"(\w+)=([^ ]+)", line))
        for line in output.splitlines() if line.startswith("CYCLE ")
    ]
    if len(rows) != EXPECTED_CYCLES:
        raise RuntimeError("expected %d cycle rows, got %d" %
                           (EXPECTED_CYCLES, len(rows)))
    for row in rows:
        if set(row) != set(WIDTHS) | {"resetn", "mem_ready", "mem_rdata"}:
            raise RuntimeError("cycle row fields changed: %s" % sorted(row))
    return rows


def check_program(rows: list[dict[str, str]]) -> None:
    retired = [row for row in rows if row["rvfi_valid"] == "1"]
    words = [format(int(row["rvfi_insn"], 2), "08x") for row in retired[:9]]
    expected = [
        "00500093", "00700113", "002081b3", "10302023",
        "10002203", "00418463", "02a00313", "000f83b3", "00100073",
    ]
    if words != expected:
        raise RuntimeError("unexpected retired program prefix: %s" % words)
    if "06300293" in words:
        raise RuntimeError("branch fall-through instruction retired")
    if retired[3]["rvfi_mem_wmask"] != "1111":
        raise RuntimeError("store row has no full-word write mask")
    if retired[4]["rvfi_mem_rmask"] != "1111":
        raise RuntimeError("load row has no full-word read mask")
    if "x" not in retired[7]["rvfi_rd_wdata"].lower():
        raise RuntimeError("uninitialized-register row did not retain x")


def lean_literal(value: str) -> str:
    return json.dumps(value.lower())


def make_lean_probe(rows: list[dict[str, str]]) -> str:
    def input_row(resetn: int, mem_ready: int, mem_rdata: int) -> str:
        return (
            "[(\"resetn\", LVec.ofNat 1 %d), "
            "(\"mem_ready\", LVec.ofNat 1 %d), "
            "(\"mem_rdata\", LVec.ofNat 32 %d), "
            "(\"pcpi_wr\", LVec.ofNat 1 0), "
            "(\"pcpi_rd\", LVec.ofNat 32 0), "
            "(\"pcpi_wait\", LVec.ofNat 1 0), "
            "(\"pcpi_ready\", LVec.ofNat 1 0), "
            "(\"irq\", LVec.ofNat 32 0)]" % (resetn, mem_ready, mem_rdata)
        )

    data_rows = [input_row(0, 1, 0) for _ in range(4)]
    for index, row in enumerate(rows):
        previous = rows[index - 1]["mem_rdata"] if index else "0" * 32
        if set(previous) - {"0", "1"}:
            raise RuntimeError("memory input contains unknown bits at cycle %d" % index)
        data_rows.append(input_row(1, int(row["mem_ready"], 2), int(previous, 2)))

    output_names = [name for name in rows[0] if name in WIDTHS]
    expected_rows = []
    for row in rows:
        fields = []
        for name in output_names:
            value = row[name].lower()
            if len(value) != WIDTHS[name]:
                raise RuntimeError("field width changed for %s" % name)
            fields.append("(%s, %s)" % (json.dumps(name), lean_literal(value)))
        expected_rows.append("[" + ", ".join(fields) + "]")

    observed = ", ".join(
        "(%s, SvState.showSignal v %s)" % (json.dumps(name), json.dumps(name))
        for name in output_names
    )
    return """import Examples.«system-verilog».cores.picorv32.input_drive_core
open LeanModels.Sv LeanModels.Sv.Kernel
namespace Examples.«system-verilog».cores.picorv32
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
def lowEntry (clk : String) (data : SvState) : SvState := (clk, ⟨#[.l0]⟩) :: data
def highEntry (clk : String) : SvState := [(clk, ⟨#[.l1]⟩)]
def rows : List SvState := [
  %s
]
def runRows (d : CoreMemDesign) (s : CoreMemState) : List SvState → Res (List CoreMemState)
 | [] => .ok []
 | row :: rest => do
   let s' ← d.fastStepCanonical s (lowEntry "clk" row)
   let s'' ← d.fastStepCanonical s' (highEntry "clk")
   let tail ← runRows d s'' rest
   .ok (s'' :: tail)
def sigs (d : CoreMemDesign) (ss : List CoreMemState) : List (List (String × String)) :=
 ss.drop 4 |>.map fun s => let v := d.scalar.view s.scalar
   [%s]
def expected : List (List (String × String)) := [
  %s
]
#eval match picorv32_core_mem with
| .ok d => match runRows d d.initial rows with
 | .ok ss => if sigs d ss == expected then "ok" else "mismatch"
 | .unsupported msg => "step refusal: " ++ msg
 | .timeout => "step timeout"
| .unsupported msg => "load refusal: " ++ msg
| .timeout => "load timeout"
end Examples.«system-verilog».cores.picorv32
""" % (",\n  ".join(data_rows), observed,
       ",\n  ".join(expected_rows))


def canonical_e_run(rows: list[dict[str, str]]) -> str:
    run(["lake", "build", "Examples.«system-verilog».cores.picorv32.input_drive_core"], ROOT)
    with tempfile.NamedTemporaryFile(
        mode="w", suffix=".lean", prefix="picorv32-e-run-",
        dir=ROOT / ".lake", delete=False,
    ) as handle:
        handle.write(make_lean_probe(rows))
        probe = Path(handle.name)
    try:
        output = run(["lake", "env", "lean", str(probe)], ROOT)
    finally:
        probe.unlink(missing_ok=True)
    return replay_result(output)


def replay_result(output: str) -> str:
    result = output.strip()
    if result == '"ok"':
        return ""
    if result == json.dumps("load refusal: " + EXPECTED_LOAD_REFUSAL, ensure_ascii=False):
        return EXPECTED_LOAD_REFUSAL
    raise RuntimeError("unexpected canonical-E result\n" + output)


def main() -> int:
    for path, digest in ((SOURCE, SOURCE_SHA256),
                         (ENVELOPE, ENVELOPE_SHA256),
                         (TESTBENCH, TESTBENCH_SHA256)):
        if sha256(path) != digest:
            raise RuntimeError("pinned hash mismatch: " + str(path))
    iverilog = run(["iverilog", "-V"], ROOT)
    if "Icarus Verilog version 13.0" not in iverilog:
        raise RuntimeError("unexpected Icarus version")
    xrun = run(["xrun", "-version"], ROOT)
    if "24.03-s004" not in xrun:
        raise RuntimeError("unexpected Xcelium version")
    with tempfile.TemporaryDirectory(prefix="picorv32-e-run-", dir=ROOT / ".lake") as work:
        directory = Path(work)
        ivvp = directory / "ivvp"
        run(["iverilog", "-g2012", "-DRISCV_FORMAL", "-s",
             "tb_picorv32_rvfi_long", "-o", str(ivvp), str(SOURCE), str(TESTBENCH)], directory)
        icarus = parse_rows(run(["vvp", str(ivvp)], directory))
        xcelium = parse_rows(run(["xrun", "-sv", "-q", "-define", "RISCV_FORMAL",
                                  "-top", "tb_picorv32_rvfi_long", str(SOURCE), str(TESTBENCH)], directory))
    if icarus != xcelium:
        raise RuntimeError("simulator traces differ")
    if sha256(TRANSCRIPT) != TRANSCRIPT_SHA256:
        raise RuntimeError("checked-in simulator transcript hash mismatch")
    transcript = parse_rows(TRANSCRIPT.read_text())
    if transcript != icarus:
        raise RuntimeError("checked-in simulator transcript differs from current rows")
    check_program(icarus)
    load_refusal = canonical_e_run(icarus)
    digest = hashlib.sha256("\n".join(
        " ".join("%s=%s" % pair for pair in sorted(row.items()))
        for row in icarus
    ).encode()).hexdigest()
    print("Icarus Verilog 13.0 (s20250103-64-gdad78d525) and Xcelium 24.03-s004 agree on %d/%d cycles" %
          (len(icarus), EXPECTED_CYCLES))
    print("source SHA-256: " + SOURCE_SHA256)
    print("envelope SHA-256: " + ENVELOPE_SHA256)
    print("testbench SHA-256: " + TESTBENCH_SHA256)
    print("simulator transcript SHA-256: " + TRANSCRIPT_SHA256)
    print("normalized binary cycle-row SHA-256: " + digest)
    if load_refusal:
        print("canonical-E: 0/%d cycles; design instantiation refused before reset: %s" %
              (len(icarus), load_refusal))
    else:
        print("canonical-E: %d/%d cycles and all %d observed outputs match" %
              (len(icarus), len(icarus), len(WIDTHS)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
