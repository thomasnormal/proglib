/-
Canonical-E receipt for the time-zero continuous-assignment quiescence rule.
IEEE 1800-2023 §§4.5 and 10.3 require the active region to remain live until
continuous drivers are current.  The edge-source rows also exercise §4.7's
time-zero ordering boundary.  The canonical route settles both assignment
orders before the first slot, so the two edge designs have the same result.
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.time_zero_quiesce_e

open LeanModels.Sv LeanModels.Sv.Kernel

load_design_sv2 nontopo from
  "Examples/system-verilog/sem2/time_zero_quiesce_e/time_zero_quiesce_nontopo.sv.json"
load_design_sv2 gclk from
  "Examples/system-verilog/sem2/time_zero_quiesce_e/time_zero_quiesce_gclk.sv.json"
load_design_sv2 gclk2 from
  "Examples/system-verilog/sem2/time_zero_quiesce_e/time_zero_quiesce_gclk2.sv.json"

def initialSignal (r : Res CoreMemDesign) (name value : String) : Bool :=
  match r with
  | .ok d => match d.initialState with
    | .ok s => (CoreMemState.view d s).lookup name == some (LVec.lit value)
    | .timeout => false
    | .unsupported _ => false
  | .timeout => false
  | .unsupported _ => false

def firstRows (r : Res CoreMemDesign) : Res (List String) := do
  let d ← r
  let s ← d.initialState
  let states ← runCoreMemRows d s [[("d", LVec.lit "1")]]
  .ok (states.map fun st => SvState.showSignal (CoreMemState.view d st) "q")

#guard initialSignal nontopo.e "a" "1"
#guard coreMemEventSources gclk.pdesign.processes == ["g"]
#guard coreMemTimeZeroSourceWrites gclk.pdesign.processes.head! == ["g"]
#guard coreMemTimeZeroSourceWrites gclk2.pdesign.processes.head! == ["g"]
#guard initialSignal nontopo.e "b" "1"


#guard match coreMemTimeZeroEventSourceViol gclk.pdesign [] with
  | some (_, msg) => msg.contains "4.7/9.4.2"
  | none => false
#guard match PDesign.instantiateCoreMem gclk.pdesign [] with
  | .unsupported msg => msg.contains "4.7/9.4.2"
  | _ => false
#guard match PDesign.instantiateCoreMem gclk2.pdesign [] with
  | .unsupported msg => msg.contains "4.7/9.4.2"
  | _ => false

end Examples.«system-verilog».sem2.time_zero_quiesce_e
