import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.ibex_lockstep_offset_e
open LeanModels.Sv

/- The source-shaped package function is retained by Slang, but the ordinary
route refuses this unimplemented constant-function body loudly. -/
load_design_sv2 p from
  "Examples/system-verilog/sem2/ibex_lockstep_offset_e/ibex_lockstep_offset_e.sv.json"

end Examples.«system-verilog».sem2.ibex_lockstep_offset_e
