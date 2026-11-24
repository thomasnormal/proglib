import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
import LeanModels.Sv.SeqCycleObl

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».sem2.clocked_derived_shift_e

load_design_sv2 derivedShift from
  "Examples/system-verilog/sem2/clocked_derived_shift_e/clocked_derived_shift_e.sv.json"

set_option maxRecDepth 100000 in
#guard match PDesign.instantiateCoreMem derivedShift.pdesign [4] with
  | .ok E => E.topoC == true && E.oblDrivers == true && E.oblInputsUndriven == true &&
      E.oblSources == true && E.oblNoSourceRead == true && E.oblEdgeOrder == true &&
      E.oblConverted == true
  | _ => false

end Examples.«system-verilog».sem2.clocked_derived_shift_e
