import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleStages

/-!
# What the clocked profile refuses among the route's newer constructs, and why

The route (`CoreMemDesign.step`) gained three constructs beside the clocked views (`SeqCycle.lean`): a plain `always`
with an explicit event list, kept as an event process (`CoreMemProc.event`); a read of an unpacked aggregate member
(`PExpr.aggregateMember`, evaluated against the route's aggregate store); and nets with several continuous drivers,
resolved per bit (`CoreMemDesign.resolvedNets`, IEEE 1800-2023 §6.6). The clocked views mirror none of them, so the
profiles (`SeqProfile`, `SeqProfileI`) exclude each one and every refinement theorem keeps that exclusion as part of its
profile hypothesis:

* an event process is outside `ProcOkI` (and `ProcOk`);
* an aggregate-member read is outside the function-free fragment (`PExpr.hasFunctionCall` classifies it with the calls),
  which every continuous assign and every edge body of the profile must be in;
* `SeqProfileI.noResolved : E.resolvedNets = []`, and a continuous assign of the profile does not drive a resolved net.

The structure stage refuses each with its reason; the two designs below are fixtures of the semantics lane, loaded as
they are (`event_control_repro`: `always @(a or b)` beside a flip-flop; `resolved_net_canonical_e`: two continuous
drivers of one wire).
-/

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».seq_cycle.seq_refusals

load_design_sv2 ev from "Examples/system-verilog/event_control_repro/event_control_repro.sv.json"
set_option maxRecDepth 100000 in
load_design_sv2 rn from "Examples/system-verilog/sem2/resolved_net_canonical_e/resolved_net_canonical_e.sv.json"

/-! ## The definitions' boundary -/

/-- No event process is in the instant profile. -/
example (E : CoreMemDesign) (i : Nat) (es : List CoreMemEvent) (b : PStmt) : ¬ E.ProcOkI i (.event es b) := by
  simp [CoreMemDesign.ProcOkI]

/-- No event process is in the single-clock profile. -/
example (E : CoreMemDesign) (clk : String) (i : Nat) (es : List CoreMemEvent) (b : PStmt) :
    ¬ E.ProcOk clk i (.event es b) := by
  simp [CoreMemDesign.ProcOk]

/-- An aggregate-member read is outside the function-free fragment the profile requires. -/
example (base : String) (path : List (Option String × Option PExpr)) :
    LeanModels.Sv.PExpr.hasFunctionCall (.aggregateMember base path) = true := rfl

/-- A continuous assign of the profile does not drive a resolved net. -/
example (E : CoreMemDesign) (i : Nat) (n : String) (v : PExpr) (h : E.ProcOkI i (.assign (.ident n) v)) :
    n ∉ E.resolvedNets := h.2.2.2

/-- A design in the instant profile has no resolved net. -/
example (E : CoreMemDesign) (hP : E.SeqProfileI) : E.resolvedNets = [] := hP.noResolved

/-! ## The structure stage's refusals -/

#guard (match ev.e with | .ok E => E.processes.size == 2 | _ => false)
#guard (match rn.e with | .ok E => E.resolvedNets == ["y"] | _ => false)

/--
error: sv_structure: process 0 is a plain `always` with an explicit event list (`always @(a or b)`, kept as an event process): its event control is not one clock edge with an optional asynchronous reset, outside the clocked profile, refused
-/
#guard_msgs (whitespace := lax) in
example : SeqDesignI ev.e := by
  sv_structure

/--
error: sv_structure: process 0 (a continuous assign) drives `y`, a net with several continuous drivers: the clocked views do not model the §6.6 driver resolution (`resolvedNets`), refused
-/
#guard_msgs (whitespace := lax) in
example : SeqDesignI rn.e := by
  sv_structure

end Examples.«system-verilog».seq_cycle.seq_refusals
