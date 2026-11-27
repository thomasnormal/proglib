/-
Canonical-E refusal for a level-sensitive event reader that observes an
always_comb result whose inputs wake both processes. IEEE 1800-2023
§§9.2.2.2 and 9.4.2 leave their activation order open.
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.level_event_comb_race_e.agree

open LeanModels.Sv LeanModels.Sv.Kernel

load_design_sv2 levelEventCombRace
  from "Examples/system-verilog/sem2/level_event_comb_race_e/level_event_comb_race_e.sv.json"

#guard match levelEventCombRace.pdesign.processes with
  | [.alwaysEvent [{ signal := "a", edge := .any },
                   { signal := "b", edge := .any },
                   { signal := "en", edge := .any }] _,
     .alwaysComb _] => true
  | _ => false

#guard match levelEventCombRace.e with
  | .unsupported msg => msg.startsWith "Schedule:level-event"
  | _ => false

end Examples.«system-verilog».sem2.level_event_comb_race_e.agree
