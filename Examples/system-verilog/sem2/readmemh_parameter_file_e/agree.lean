/- `$readmemh` resolves an elaboration-time string parameter as its filename.
   A missing file leaves the memory unchanged under IEEE 1800-2023 §21.4. -/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.readmemh_parameter_file_e

open LeanModels.Sv LeanModels.Sv.Kernel

load_design_sv2 readmemhParameterFile
  from "Examples/system-verilog/sem2/readmemh_parameter_file_e/readmemh_parameter_file.sv.json"

private def valuesMem : Nat := 559036394418041707652461

#guard readmemhParameterFile.pdesign.readmemh.length == 1
#guard match readmemhParameterFile.pdesign.readmemh with
  | [{ file := "values.mem", target := "mem", words := [] }] => true
  | _ => false

def outputs : Res (List String) := do
  let d ← readmemhParameterFile.e valuesMem 8 4
  let st ← d.initialState
  let states ← runCoreMemRows d st [[]]
  .ok (states.map fun s => SvState.showSignal (CoreMemState.view d s) "y")

#eval outputs

end Examples.«system-verilog».sem2.readmemh_parameter_file_e
