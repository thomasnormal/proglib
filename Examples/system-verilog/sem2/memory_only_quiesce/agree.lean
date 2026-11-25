import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.memory_only_quiesce
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 memoryOnlyQuiesce from "Examples/system-verilog/sem2/memory_only_quiesce/memory_only_quiesce.sv.json"
def fmt (d : CoreMemDesign) (s : CoreMemState) : String :=
  let m0 := s.memory.read "mem" 0
  let m1 := s.memory.read "mem" 1
  let tag0 := if m0 == some (LVec.ofNat 1 0) then "0" else if m0 == some (LVec.ofNat 1 1) then "1" else "x"
  let tag1 := if m1 == some (LVec.ofNat 1 0) then "0" else if m1 == some (LVec.ofNat 1 1) then "1" else "x"
  "q=" ++ SvState.showSignal (CoreMemState.view d s) "q" ++ ",mem=" ++ tag0 ++ tag1
def result : String := match PDesign.instantiateCoreMem memoryOnlyQuiesce.pdesign [] with
  | .ok d => match d.initialState with
    | .ok s => match runCoreMemRows d s [[("seed", LVec.ofNat 1 0)], [("seed", LVec.ofNat 1 1)]] with
      | .ok states => String.intercalate "|" (states.map (fmt d))
      | .timeout => "timeout"
      | .unsupported msg => msg
    | .timeout => "initial-timeout"
    | .unsupported msg => "initial:" ++ msg
  | .timeout => "design-timeout"
  | .unsupported msg => "design:" ++ msg
#eval result
end Examples.«system-verilog».sem2.memory_only_quiesce
