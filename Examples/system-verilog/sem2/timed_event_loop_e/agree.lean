import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.timed_event_loop_e
open LeanModels.Sv
load_design_sv2 timedEventLoopE from
  "Examples/system-verilog/sem2/timed_event_loop_e/timed_event_loop_e.sv.json"
#guard timedEventLoopE.pdesign.others == []
#guard match timedEventLoopE.sem.processes.toList with
  | [.alwaysComb (.block #[.blockingAssign (.ident "y") _, .block arms])] => arms.size == 8
  | _ => false

def outputs : Res (List String) := do
  let rows ← run2 timedEventLoopE.sem σ_src 4096 [
    [("x", LVec.lit "00000000")], [("x", LVec.lit "00000001")],
    [("x", LVec.lit "10100100")], [("x", LVec.lit "11111111")],
    [("x", LVec.lit "xxxxxxxx")]]
  pure (rows.map (SvState.showSignal · "y"))

#guard outputs == .ok ["0000", "0000", "0111", "0111", "0000"]
end Examples.«system-verilog».sem2.timed_event_loop_e
