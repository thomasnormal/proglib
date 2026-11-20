import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleStages

/-!
# What the clocked profile refuses among the route's newer constructs, and why

The route (`CoreMemDesign.step`) gained three constructs beside the clocked views (`SeqCycle.lean`): a plain `always`
with an explicit event list, kept as an event process (`CoreMemProc.event`); a read of an unpacked aggregate member
(`PExpr.aggregateMember`, evaluated against the route's aggregate store); and nets with several continuous drivers,
resolved per bit (`CoreMemDesign.resolvedNets`, IEEE 1800-2023 §6.6). The clocked views read an event process whose
event list is one clock edge with an optional asynchronous reset edge as its edge process (`CoreMemProc.edge?`,
`seq_cycle/plain_proof`); they mirror nothing else of the three, so the profiles (`SeqProfile`, `SeqProfileI`) exclude
the rest and every refinement theorem keeps that exclusion as part of its profile hypothesis:

* an event process with a level-change member (`always @(a or b)`) or more than two events is outside `ProcOkI` (and
  `ProcOk`); one that names its reset first is in the profile, with the first edge as its clock, and is refused by the
  obligation that no body reads its clock;
* an aggregate-member read is outside the function-free fragment (`PExpr.hasFunctionCall` classifies it with the calls),
  which every continuous assign and every edge body of the profile must be in;
* `SeqProfileI.noResolved : E.resolvedNets = []`, and a continuous assign of the profile does not drive a resolved net.

The structure stage refuses each with its reason; the two designs below are fixtures of the semantics lane, loaded as
they are (`event_control_repro`: `always @(a or b)` beside a flip-flop; `resolved_net_canonical_e`: two continuous
drivers of one wire). `seq_neg/plain_three_events` (a clock, a reset and a set edge) and `seq_neg/plain_reset_first`
(`always @(negedge rst_n or posedge clk)`) pin the two plain-`always` refusals that remain.

When every process, the memories and the resolved nets pass but the profile still does not hold, the stage names the
conjunct that fails (the edge view, distinct names, 4-state declarations, or the whole-list process check) instead of
one generic message; `seq_neg/two_state_reg` (a flip-flop on `bit` data) pins the 4-state one.
-/

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».seq_cycle.seq_refusals

load_design_sv2 ev from "Examples/system-verilog/event_control_repro/event_control_repro.sv.json"
set_option maxRecDepth 100000 in
load_design_sv2 rn from "Examples/system-verilog/sem2/resolved_net_canonical_e/resolved_net_canonical_e.sv.json"
load_design_sv2 ts from "Examples/system-verilog/seq_neg/two_state_reg.sv.json"
load_design_sv2 p3 from "Examples/system-verilog/seq_neg/plain_three_events.sv.json"
load_design_sv2 prf from "Examples/system-verilog/seq_neg/plain_reset_first.sv.json"

/-! ## The definitions' boundary -/

/-- A plain `always` on one clock edge with an asynchronous reset edge is its edge process. -/
example (b : PStmt) :
    (CoreMemProc.event [⟨"clk", .posedge⟩, ⟨"rst_n", .negedge⟩] b).edge? =
      some { clock := "clk", edge := .posedge, reset := some "rst_n", resetHigh := false, body := b,
             style := .alwaysPlain } := rfl

/-- An event process with a level-change member is no edge process: outside the instant profile. -/
example (E : CoreMemDesign) (i : Nat) (b : PStmt) :
    ¬ E.ProcOkI i (.event [⟨"a", .any⟩, ⟨"b", .any⟩] b) := by
  simp [CoreMemDesign.ProcOkI, coreMemEventEdge?, CoreMemEvent.clockEdge?]

/-- An event process on three edges is no edge process: outside the single-clock profile (and the instant one). -/
example (E : CoreMemDesign) (clk : String) (i : Nat) (b : PStmt) :
    ¬ E.ProcOk clk i (.event [⟨"clk", .posedge⟩, ⟨"rst_n", .negedge⟩, ⟨"set", .posedge⟩] b) := by
  simp [CoreMemDesign.ProcOk, coreMemEventEdge?]

/-- An event process that is no edge process has no event, is skipped by the view-level edge pass and drives nothing
the obligations see: the profile excludes it, the definitions do not guess at it. -/
example (b : PStmt) : (CoreMemProc.event [⟨"a", .any⟩] b).edge? = none := rfl

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
error: sv_structure: process 1 is a plain `always` whose event list is not one clock edge with an optional asynchronous reset edge (a level-change event as in `always @(a or b)`, or more than two events; kept as an event process): outside the clocked profile, refused
-/
#guard_msgs (whitespace := lax) in
example : SeqDesignI ev.e := by
  sv_structure

/--
error: sv_structure: process 0 is a plain `always` whose event list is not one clock edge with an optional asynchronous reset edge (a level-change event as in `always @(a or b)`, or more than two events; kept as an event process): outside the clocked profile, refused
-/
#guard_msgs (whitespace := lax) in
example : SeqDesignI p3.e := by
  sv_structure

/--
error: sv_structure: obligation `oblNoSourceRead`: a process reads an event source as data (a continuous assign reading a clock or reset, or an edge body reading a clock or another process's reset: in an instant it could read either value, §4.7), refused
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (h1 : 1 ≤ N) (h2 : N < 2 ^ 30) : SeqDesignI (prf.e N) := by
  sv_structure

/--
error: sv_structure: process 0 (a continuous assign) drives `y`, a net with several continuous drivers: the clocked views do not model the §6.6 driver resolution (`resolvedNets`), refused
-/
#guard_msgs (whitespace := lax) in
example : SeqDesignI rn.e := by
  sv_structure

/--
error: sv_structure: the clocked profile does not hold: a declaration is 2-state (`bit`, `int`, …): the clocked views are 4-state (`AllFour`), refused
-/
#guard_msgs (whitespace := lax) in
example : SeqDesign ts.e "clk" := by
  sv_structure

end Examples.«system-verilog».seq_cycle.seq_refusals
