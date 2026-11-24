import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleStages

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».sem2.clocked_tick_assign_e

load_design_sv2 tick from "Examples/system-verilog/sem2/clocked_tick_assign_e/clocked_tick_assign.sv.json"

example : SeqDesignI tick.e := by
  sv_structure

#guard (match tick.e with | .ok E => E.topoC == true | _ => false)

end Examples.«system-verilog».sem2.clocked_tick_assign_e
