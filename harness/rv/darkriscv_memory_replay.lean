import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemFast

/-! Replay the pre-posedge rows of the pinned DarkRISCV RV32UI memory tests.
Each input vector comes from the memory testbench. Every expected output is
checked against the loaded core before advancing the clock. -/
open LeanModels.Sv LeanModels.Sv.Kernel

load_design_sv2 dark from "Examples/system-verilog/cores/darkriscv/darkriscv.sv.json"

private def checked {α : Type} (where_ : String) : Res α → IO α
  | .ok a => pure a
  | .unsupported msg => throw (IO.userError s!"{where_}: {msg}")
  | .timeout => throw (IO.userError s!"{where_}: timeout")

private def inputs : List (String × Nat) :=
  [("RES", 1), ("IDATA", 32), ("IDACK", 1), ("DATAI", 32), ("DDACK", 1)]

private def observed : List String :=
  ["IDREQ", "IADDR", "DDREQ", "DADDR", "DLEN", "DBE", "DRW", "DRD", "DWR", "DATAO",
   "DEBUG", "ESIMACK", "XRES", "HLT", "FLUSH", "PC", "XIDATA", "IERR"]

private def registers : List Nat := [3, 10, 17]

private def replay (d : CoreMemDesign) (file : String) : IO Unit := do
  let mut st ← checked "initial state" d.initialState
  let mut cycles := 0
  for line in (← IO.FS.lines file) do
    let fields := line.splitOn " "
    unless fields.take 2 == ["ROW", toString cycles] &&
        fields.length == 2 + inputs.length + observed.length + registers.length do
      throw (IO.userError s!"{file}:{cycles}: malformed row")
    let mut row : SvState := [("CLK", LVec.ofNat 1 0), ("IRQ", LVec.ofNat 1 0),
      ("IBERR", LVec.ofNat 1 0), ("DBERR", LVec.ofNat 1 0), ("ESIMREQ", LVec.ofNat 1 0)]
    for ((name, width), digits) in inputs.zip (fields.drop 2) do
      let some value := LVec.ofString? digits
        | throw (IO.userError s!"{name}: invalid input {digits}")
      unless value.width == width do throw (IO.userError s!"{name}: wrong width {digits}")
      row := (name, value) :: row
    let low ← checked s!"{file}:{cycles}: input drive" (d.fastStepCanonical st row)
    let view := d.scalar.view low.scalar
    let samples := fields.drop (2 + inputs.length)
    for (name, expected) in observed.zip samples do
      let actual := SvState.showSignal view name
      unless actual == expected do
        throw (IO.userError s!"{file}:{cycles}: {name} E={actual} simulator={expected}")
    for (index, expected) in registers.zip (samples.drop observed.length) do
      let actual := ((low.memory.read "REGS" index).map LVec.toBinString).getD "<absent>"
      unless actual == expected do
        throw (IO.userError s!"{file}:{cycles}: x{index} E={actual} simulator={expected}")
    st ← checked s!"{file}:{cycles}: posedge" (d.fastStepCanonical low [("CLK", LVec.ofNat 1 1)])
    cycles := cycles + 1
  if cycles == 0 then throw (IO.userError s!"{file}: empty trace")
  IO.println s!"{file}: {cycles} cycles agree"

def main (args : List String) : IO Unit := do
  if args.isEmpty then throw (IO.userError "expected one or more simulator trace paths")
  let d ← checked "DarkRISCV instantiation" (dark.e 0)
  for file in args do replay d file
