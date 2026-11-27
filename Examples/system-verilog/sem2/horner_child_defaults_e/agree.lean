/- Child parameter forwarding keeps the parser's string metadata and the
   integer dimensions supplied by the parent (§6.20.2, §23.3). -/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.HierarchyCoreMem
namespace Examples.«system-verilog».sem2.horner_child_defaults_e
open LeanModels.Sv LeanModels.Sv.Kernel

load_design_sv2 horner from
  "Examples/system-verilog/sem2/horner_child_defaults_e/horner_child_defaults.sv.json"

private def romStyle : Nat := 121390560208617634159420772
#guard horner.pdesign.defaultArgs == .ok [8, 2, 2, romStyle]
#guard match horner.e 8 2 2 romStyle with | .ok d => CoreMemDesign.Structure d | _ => false

def rows : IO (Res (List String)) := do
  let d ← match horner.e 8 2 2 romStyle with
    | .ok d => pure d
    | .timeout => throw (IO.userError "instantiate timeout")
    | .unsupported e => throw (IO.userError e)
  let rows ← match runCoreMemRows d d.initial [
      [("address", LVec.lit "00"), ("t", LVec.lit "00000000")],
      [("address", LVec.lit "10"), ("t", LVec.lit "10100101")],
      [("address", LVec.lit "10"), ("t", LVec.lit "xxxxxxxx")],
      [("address", LVec.lit "10"), ("t", LVec.lit "zzzzzzzz")]] with
    | .ok rows => pure rows
    | .timeout => throw (IO.userError "run timeout")
    | .unsupported e => throw (IO.userError e)
  pure (.ok (rows.map fun s => SvState.showSignal (CoreMemState.view d s) "value"))

#eval rows

end Examples.«system-verilog».sem2.horner_child_defaults_e
