import Examples.«system-verilog».cores.picorv32.input_drive_core

/-! Drive the input values sampled by the PicoRV32 memory testbench, then
compare each output after the rising edge, including all four reset clocks. -/
open LeanModels.Sv LeanModels.Sv.Kernel
open Examples.«system-verilog».cores.picorv32

namespace PicoInputReplay

private def checked {α : Type} (stage : String) : Res α → IO α
  | .ok value => pure value
  | .unsupported msg => throw (IO.userError s!"{stage}: {msg}")
  | .timeout => throw (IO.userError s!"{stage}: timeout")

private def input (fields : List (String × String)) (name : String) (width : Nat) : IO LVec := do
  let some digits := fields.lookup name | throw (IO.userError s!"missing input {name}")
  let some value := LVec.ofString? digits | throw (IO.userError s!"bad input {name}={digits}")
  unless value.width == width do throw (IO.userError s!"{name}: expected {width} bits")
  return value

def replay (d : CoreMemDesign) (file : String) : IO Nat := do
  let mut state ← checked "initial state" d.initialState
  let mut samples : Nat := 0
  let design := d.scalar.toDesign2
  let inputs := design.decls.filter (fun port => port.isInput && port.name != "clk")
  let outputs := design.outputNames
  for line in ← IO.FS.lines file do
    let cycle := (samples : Int) - 4
    let site := s!"{file} cycle {cycle}"
    let "CYCLE" :: index :: words := line.splitOn " " | throw (IO.userError s!"{site}: malformed row")
    unless index == toString cycle do throw (IO.userError s!"{site}: wrong cycle number {index}")
    let fields ← words.mapM fun word => do
      let [name, digits] := word.splitOn "=" | throw (IO.userError s!"{site}: malformed field")
      pure (name, digits)
    -- The post-edge mem_rdata in the trace may already be the response to
    -- the next address. sampled_rdata was captured before the NBA updates.
    let mut row : SvState := [("clk", .ofNat 1 0)]
    for port in inputs do
      let field := if port.name == "mem_rdata" then "sampled_rdata" else port.name
      row := (port.name, ← input fields field port.width) :: row
    let low ← checked s!"{site} input drive" (d.fastStepCanonical state row)
    state ← checked s!"{site} posedge" (d.fastStepCanonical low [("clk", .ofNat 1 1)])
    let view := d.scalar.view state.scalar
    for name in outputs do
      let some expected := fields.lookup name | throw (IO.userError s!"{site}: missing output {name}")
      let actual := SvState.showSignal view name
      unless actual == expected do throw (IO.userError s!"{site}: {name} E={actual} simulator={expected}")
    samples := samples + 1
  if samples <= 4 then throw (IO.userError s!"{file}: no post-reset samples")
  return samples

end PicoInputReplay

def main (files : List String) : IO Unit := do
  if files.isEmpty then throw (IO.userError "expected PicoRV32 cycle rows")
  match picorv32_core_mem with
  | .unsupported msg => IO.println s!"load refusal: {msg}"
  | .timeout => throw (IO.userError "PicoRV32 load timeout")
  | .ok d =>
      for file in files do
        let count ← PicoInputReplay.replay d file
        IO.println s!"{count} samples, {d.scalar.toDesign2.outputNames.size} outputs agree"
