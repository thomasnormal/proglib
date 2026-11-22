#!/usr/bin/env python3
"""Run the bundled DarkRISCV three-way battery and its negative control."""
from __future__ import annotations

import hashlib
import os
import re
import subprocess
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
TMPDIR = Path(os.environ.get("TMPDIR", str(ROOT / ".lake" / "tmp")))
SOURCE = HERE / "rtl" / "darkriscv.v"
ENVELOPE = HERE / "darkriscv.sv.json"
PINNED_SOURCE = "46d57b15cc42c0458e02500a2a30371cd4e7979970c27afd9d47c40d1fa8c1a0"
PINNED_ENVELOPE = "ca7ba5a2e87ea6a1c2c0eb6b4975ac1a5c1787999241c4ba777adb25de82cd32"
EXPECTED_CYCLES = 1000

sys.path.insert(0, str(HERE))
from check import run_receipt  # noqa: E402


# Every field printed by the testbench is checked against the canonical scalar
# view after the same rising edge.  Hex simulator values become fixed-width
# binary strings so x/z and width changes cannot be hidden by formatting.
FIELDS = (
    ("reset", "RES", 1), ("instr_req", "IDREQ", 1),
    ("instr_addr", "IADDR", 32), ("instr_data", "IDATA", 32),
    ("data_req", "DDREQ", 1), ("data_addr", "DADDR", 32),
    ("data_len", "DLEN", 3), ("data_be", "DBE", 4),
    ("data_rw", "DRW", 1), ("data_rd", "DRD", 1),
    ("data_wr", "DWR", 1), ("data_out", "DATAO", 32),
    ("data_in", "DATAI", 32), ("data_ack", "DDACK", 1),
    ("debug", "DEBUG", 4),
)


def parse_rows(lines: list[str], cycles: int | None = None, *,
               observe_x2: bool = False) -> list[dict[str, str]]:
    rows = [dict(re.findall(r"(\w+)=([^ ]+)", line)) for line in lines]
    cycles = EXPECTED_CYCLES if cycles is None else cycles
    if len(rows) != cycles:
        raise RuntimeError(f"expected {cycles} simulator rows, got {len(rows)}")
    for row in rows:
        row.setdefault("instr_ack", "1")
    required = {name for name, _, _ in FIELDS} | {"cycle", "instr_ack"}
    if observe_x2:
        required.update(("x2", "esimack"))
    for row in rows:
        if set(row) != required:
            raise RuntimeError(f"simulator row fields changed: {sorted(row)}")
    return rows


def bits(raw: str, width: int) -> str:
    if len(raw) == width and set(raw) <= {"0", "1", "x", "z"}:
        return raw.lower()
    if len(raw) != width // 4 and set(raw) <= {"0", "1", "x", "z"}:
        raise RuntimeError(f"binary field has wrong width: {raw} for {width}")
    return format(int(raw, 16), f"0{width}b")


def expected_rows(lines: list[str], cycles: int | None = None, *,
                  observe_x2: bool = False) -> list[list[tuple[str, str]]]:
    fields = FIELDS + (("instr_ack", "IDACK", 1),)
    return [
        [(lean_name, bits(row[sim_name], width)) for sim_name, lean_name, width in fields]
        + [("CLK", "1")]
        + ([("ESIMACK", bits(row["esimack"], 1)), ("REGS[2]", bits(row["x2"], 32))] if observe_x2 else [])
        for row in parse_rows(lines, cycles, observe_x2=observe_x2)
    ]


def lean_string(value: str) -> str:
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'


def lean_rows(rows: list[list[tuple[str, str]]]) -> str:
    return "[\n" + ",\n".join(
        "  [" + ", ".join(
            f"({lean_string(name)}, {lean_string(value)})" for name, value in row
        ) + "]"
        for row in rows
    ) + "\n]"


def make_probe(rows: list[list[tuple[str, str]]], corrupted: list[list[tuple[str, str]]]) -> str:
    expected = lean_rows(rows)
    wrong = lean_rows(corrupted)
    stimuli = []
    for fields in rows:
        row = dict(fields)
        idata, ddack, idack = (int(row[name], 2) for name in ("IDATA", "DDACK", "IDACK"))
        data = row["DATAI"]
        if len(data) != 32 or set(data) - set("01xz"):
            raise ValueError(f"invalid 32-bit DATAI: {data}")
        stimuli.append(f'  ({idata}, {ddack}, {idack}, LVec.lit "{data}")')
    stimulus = ",\n".join(stimuli)
    sim_control = ""
    sim_output = ""
    register_sample = ""
    if "REGS[2]" in dict(rows[0]):
        sim_control = ', ("ESIMREQ", bits 1 0)'
        sim_output = ', "ESIMACK"'
        register_sample = ' ++ [("REGS[2]", ((s.memory.read "REGS" 2).map LVec.toBinString).getD "<absent>")]'
    return f'''import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemFast
open LeanModels.Sv LeanModels.Sv.Kernel
set_option maxRecDepth 100000
set_option maxHeartbeats 6000000
load_design_sv2 dark from "{ENVELOPE}"
def bits (w n : Nat) := LVec.ofNat w n
def row (res : Nat) (clk : Nat) (idata ddack idack : Nat) (data : LVec) : SvState := [
  ("CLK", bits 1 clk), ("RES", bits 1 res), ("IRQ", bits 1 0){sim_control},
  ("IDATA", bits 32 idata), ("IDACK", bits 1 idack), ("IBERR", bits 1 0),
  ("DATAI", data), ("DDACK", bits 1 ddack), ("DBERR", bits 1 0)]
def cycle (d : CoreMemDesign) (s : CoreMemState) (res idata ddack idack : Nat) : Res CoreMemState := do
  let low ← d.fastStepCanonical s (row res 0 idata ddack idack (bits 32 0))
  d.fastStepCanonical low (row res 1 idata ddack idack (bits 32 0))
def resetN (d : CoreMemDesign) : Nat → CoreMemState → Res CoreMemState
  | 0, s => .ok s
  | n + 1, s => do
      let s' ← cycle d s 1 19 1 1
      resetN d n s'
def runRows (d : CoreMemDesign) : CoreMemState → List (Nat × Nat × Nat × LVec) → Res (List CoreMemState)
  | s, [] => .ok []
  | s, (idata, ddack, idack, data) :: rest => do
      let low ← d.fastStepCanonical s (row 0 0 idata ddack idack data)
      let s' ← d.fastStepCanonical low (row 0 1 idata ddack idack data)
      let tail ← runRows d s' rest
      .ok (s' :: tail)
def names : List String := ["RES", "IDREQ", "IADDR", "IDATA",
  "DDREQ", "DADDR", "DLEN", "DBE", "DRW", "DRD", "DWR", "DATAO", "DATAI",
  "DDACK", "DEBUG", "IDACK", "CLK"{sim_output}]
def sigs (d : CoreMemDesign) (states : List CoreMemState) : List (List (String × String)) :=
  states.map fun s => (names.map fun name => (name, SvState.showSignal (d.scalar.view s.scalar) name)){register_sample}
def firstFieldMismatch : List (String × String) → List (String × String) → Option (String × String × String)
  | [], _ => none
  | _, [] => none
  | (an, av) :: as, (en, ev) :: es =>
      if an != en || av != ev then some (an, av, ev) else firstFieldMismatch as es
def firstMismatch : Nat → List (List (String × String)) → List (List (String × String)) → Option (Nat × String × String × String)
  | _, [], _ => none
  | _, _, [] => none
  | n, a :: as, e :: es =>
      if a == e then firstMismatch (n + 1) as es
      else match firstFieldMismatch a e with
        | some (name, actual, wanted) => some (n, name, actual, wanted)
        | none => some (n, "<row>", "<different>", "<different>")
def expected : List (List (String × String)) := {expected}
def corrupted : List (List (String × String)) := {wrong}
#eval match dark.e 0 with
| .ok d => match d.initialState with
  | .ok initial => match resetN d 4 initial with
    | .ok resetState => match runRows d resetState [
{stimulus}
      ] with
      | .ok states =>
          let actual := sigs d states
          (actual == expected, actual == corrupted, firstMismatch 0 actual expected)
      | .timeout => (false, false, none)
      | .unsupported _ => (false, false, none)
    | .timeout => (false, false, none)
    | .unsupported _ => (false, false, none)
  | .timeout => (false, false, none)
  | .unsupported _ => (false, false, none)
| .timeout => (false, false, none)
| .unsupported _ => (false, false, none)
'''


def run_lean(rows: list[list[tuple[str, str]]],
             corrupted: list[list[tuple[str, str]]] | None = None) -> tuple[bool, bool, str]:
    if corrupted is None:
        corrupted = [*rows]
        corrupted[0] = [
            (name, "1" * len(value) if name == "IADDR" else value)
            for name, value in rows[0]
        ]
    probe = ROOT / ".lake" / f"darkriscv-battery-{os.getpid()}.lean"
    probe.write_text(make_probe(rows, corrupted))
    try:
        result = subprocess.run(
            ["lake", "env", "lean", str(probe)], cwd=ROOT,
            env={**os.environ, "TMPDIR": str(TMPDIR)}, text=True,
            stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            check=False, timeout=900,
        )
    finally:
        probe.unlink(missing_ok=True)
    if result.returncode:
        raise RuntimeError(result.stdout)
    match = re.search(
        r"\((true|false), (true|false), "
        r"(none|some \(([0-9]+), \"([^\"]+)\", \"([^\"]*)\", \"([^\"]*)\"\))\)",
        result.stdout,
    )
    if match is None:
        raise RuntimeError("Lean battery produced no Boolean result\n" + result.stdout)
    if match.group(3) == "none":
        detail = "none"
    else:
        detail = (
            f"some {match.group(4)} field {match.group(5)} "
            f"actual={match.group(6)} expected={match.group(7)}"
        )
    return match.group(1) == "true", match.group(2) == "true", detail


def main() -> int:
    if hashlib.sha256(SOURCE.read_bytes()).hexdigest() != PINNED_SOURCE:
        raise SystemExit("bundled DarkRISCV source hash mismatch")
    if hashlib.sha256(ENVELOPE.read_bytes()).hexdigest() != PINNED_ENVELOPE:
        raise SystemExit("bundled DarkRISCV envelope hash mismatch")
    icarus, xcelium = run_receipt()
    if icarus != xcelium:
        raise SystemExit("the pinned simulators disagree")
    sim_rows = expected_rows(icarus)
    lean_ok, corrupted_ok, first_mismatch = run_lean(sim_rows)
    if not lean_ok:
        raise SystemExit(
            "canonical E rows differ from the simulator rows "
            f"at {first_mismatch}"
        )
    if corrupted_ok:
        raise SystemExit("negative control accepted a corrupted cycle row")
    digest = hashlib.sha256(("\n".join(icarus) + "\n").encode()).hexdigest()
    print("bundled DarkRISCV source/envelope hashes verified")
    print("Icarus Verilog 13.0 (s20250103-64-gdad78d525)")
    print("Xcelium 24.03-s004")
    print(f"three-way rows: {EXPECTED_CYCLES}/{EXPECTED_CYCLES} agree bit-for-bit")
    print(f"normalized simulator-row-sha256: {digest}")
    print("negative control: corrupted cycle row rejected by the Lean comparator")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
