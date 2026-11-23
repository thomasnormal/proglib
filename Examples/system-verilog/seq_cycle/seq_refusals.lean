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

The last section pins what stays outside among procedural loops (a `for` loop of nonblocking assignments is inside
the profile): a blocking assignment in a loop body, a `while` loop, a header the stage does not evaluate, a trip count
the hypotheses do not bound.

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
load_design_sv2 gfr from "Examples/system-verilog/seq_neg/gen_for_regs.sv.json"
load_design_sv2 gbp from "Examples/system-verilog/seq_cycle/gen_bypass.sv.json"

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

/-! ## The instantiation pass's refusals

A conditional generate construct is evaluated (`seq_cycle/gen_proof`); a generate loop is not expanded, and the stage
names it instead of printing the stuck instantiation (`seq_neg/gen_for_regs`, at symbolic and at concrete
parameters). A condition the hypotheses on the parameters do not decide is named the same way. -/

/--
error: sv_structure: the instantiation does not normalize at these parameters: a generate loop: the clocked instantiation pass does not expand a `for` generate construct (the route's `genvarSeq`; a conditional generate is evaluated), refused
-/
#guard_msgs (whitespace := lax) in
example (W : Nat) (h1 : 1 ≤ W) (h2 : W < 2 ^ 30) : SeqDesignI (gfr.e W) := by
  sv_structure

/--
error: sv_structure: the instantiation does not normalize at these parameters: a generate loop: the clocked instantiation pass does not expand a `for` generate construct (the route's `genvarSeq`; a conditional generate is evaluated), refused
-/
#guard_msgs (whitespace := lax) in
example : SeqDesignI (gfr.e 2) := by
  sv_structure

/--
error: sv_structure: the instantiation does not normalize at these parameters: the hypotheses in context do not decide `REG = 0` (a conditional generate construct takes its arm from a hypothesis on the parameters, and an `int` parameter needs both of its bounds), refused
-/
#guard_msgs (whitespace := lax) in
example (W REG : Nat) (h1 : 1 ≤ W) (h2 : W < 2 ^ 30) (h4 : REG < 2 ^ 30) : SeqDesignI (gbp.e W REG) := by
  sv_structure

/-! ## Procedural `for` loops

A procedural `for` loop of nonblocking assignments is inside the clocked profile, never unrolled
(`seq_cycle/shift_for_proof`, `seq_cycle/reset_for_proof`): the clocked views fold its body over the header's value
list as the route does. What stays outside, each refused by name:

* a loop with a BLOCKING assignment in its body (`seq_neg/for_blocking`: `acc = acc + 1` per iteration): an iteration
  reads what an earlier one wrote, so the loop is not its issued updates. The route runs it (the run below); the
  clocked views do not mirror it (`loopBodyB`; the view-level executor refuses it by name).
* a `while` loop (`seq_neg/while_loop`): ingestion keeps it unconverted and the route itself refuses it.
* a header the stage does not evaluate (`seq_neg/for_step2`: `i += 2`): the stage reads `for (i = a; i < P; i++)` and
  `i <= P` (the step `i++` or `i = i + 1`) in closed form. The route runs the loop.
* a trip count the hypotheses do not bound: the route runs a loop one unit of its statement fuel (4096) per iteration
  and answers `timeout` beyond (the run below at `N = 5000`), so a structure theorem states the bound on the parameter.

An index that is not the iterator itself (`mem[N-1-i] <= …`, `mem[2*i] <= …`) is NOT refused: the loop's write equation
`memWriteL` carries the index as its key function, and its closed form (`memWriteL_at`, `memWriteL_index`) asks for the
key to be injective on the loop's values, which the reader proves. -/

load_design_sv2 fbk from "Examples/system-verilog/seq_neg/for_blocking.sv.json"
load_design_sv2 whl from "Examples/system-verilog/seq_neg/while_loop.sv.json"
load_design_sv2 fs2 from "Examples/system-verilog/seq_neg/for_step2.sv.json"
set_option maxRecDepth 100000 in
load_design_sv2 sfr from "Examples/system-verilog/seq_cycle/shift_for.sv.json"

/-- A loop with a blocking assignment in its body is outside the edge-body fragment. -/
example (a b c e : PExpr) : (PStmt.forLoop "i" a b c (.blockingAssign "x" e)).edgeOkB = false := by
  simp [PStmt.edgeOkB, PStmt.loopBodyB]

/-- A loop nested in a loop is outside the edge-body fragment. -/
example (a b c : PExpr) (s : PStmt) : (PStmt.forLoop "i" a b c (.forLoop "j" a b c s)).edgeOkB = false := by
  simp [PStmt.edgeOkB, PStmt.loopBodyB]

/-- The view-level executor refuses such a loop by name (it never guesses at it). -/
example (E : CoreMemDesign) (env : IEnv) (v : SvState) (mv : MemV) (a b c e : PExpr) :
    E.execV env v mv (.forLoop "i" a b c (.blockingAssign "x" e)) =
      .unsupported "9.4.2: a procedural `for` loop whose body has a blocking assignment, a declaration or a nested loop is outside the clocked profile" := by
  simp [CoreMemDesign.execV, PStmt.loopBodyB]

/-- An index that is not the iterator is not refused: for the reversed loop `m[N-1-i] <= e(i)` the write equation's
closed form holds, the key being injective on the loop's values. -/
example (mv : MemV) (N : Nat) (x : Int → LVec) (i : Int) (hi : i ∈ intRange 0 N) :
    memWriteL mv "m" (intRange 0 N) (fun i => some ((N : Int) - 1 - i)) x "m" ((N : Int) - 1 - i) = x i :=
  memWriteL_index (f := fun i => (N : Int) - 1 - i) (fun _ _ => rfl)
    (fun a _ b _ h => by
      have h' : (N : Int) - 1 - a = (N : Int) - 1 - b := h
      omega) mv hi

-- The route runs the blocking loop: `q` is `d + N` (here `N = 4`, `d = 5` then `6`).
#guard (match fbk.e 4 with
  | .ok E => match runCoreMemRows E E.initial (cycleRows "clk" [[("d", .ofNat 8 5)], [("d", .ofNat 8 6)]]) with
    | .ok rows => rows.map (fun st => SvState.showSignal (CoreMemState.view E st) "q") ==
        ["xxxxxxxx", "00001001", "00001001", "00001010"]
    | _ => false
  | _ => false)

-- The route refuses the `while` loop.
#guard (match whl.e with
  | .ok E => match runCoreMemRows E E.initial (cycleRows "clk" [[("d", .ofNat 8 5)]]) with
    | .unsupported m => m == "WhileLoopStatement: while (n[7]) n = n << 1;"
    | _ => false
  | _ => false)

-- The route allocates loop fuel from the evaluated header and runs 4999 iterations.
#guard (match sfr.e 1 5000 with
  | .ok E => match runCoreMemRows E E.initial (cycleRows "clk" [[("d", .ofNat 1 1)]]) with
    | .ok _ => true
    | _ => false
  | _ => false)

/--
error: sv_structure: process 0 (an edge process) has a procedural `for` loop with a blocking assignment in its body (an iteration would read what an earlier iteration wrote): the clocked stages read a loop of nonblocking assignments only, refused
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (h1 : 1 ≤ N) (h2 : N ≤ 4000) : SeqDesign (fbk.e N) "clk" := by
  sv_structure

/--
error: sv_structure: process 0 (an edge process) holds a statement ingestion kept unconverted (WhileLoopStatement), refused
-/
#guard_msgs (whitespace := lax) in
example : SeqDesign whl.e "clk" := by
  sv_structure

/--
error: sv_structure: process 0 (an edge process) has a procedural `for` loop whose header the clocked stages do not evaluate: they read `for (i = a; i < P; i++)` and `i <= P` (a literal start `a`, a parameter bound `P`, a unit step `i++` or `i = i + 1`) as the route's value list in closed form; any other header (another step, a bound that is not a parameter, a descending loop) is refused
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (h1 : 1 ≤ N) (h2 : N ≤ 4000) : SeqDesign (fs2.e N) "clk" := by
  sv_structure

/--
error: sv_structure: process 0 (an edge process) has a procedural `for` loop whose trip count is not bounded by the route's statement fuel from the hypotheses in context: the route runs a loop one fuel unit per iteration out of 4096 and answers `timeout` beyond, so state the bound as a hypothesis on the parameters (for `for (i = a; i < N; i++)`: `N ≤ 4000`), refused
-/
#guard_msgs (whitespace := lax) in
set_option maxHeartbeats 1000000 in
example (W N : Nat) (hW1 : 1 ≤ W) (hW2 : W < 2 ^ 30) (h1 : 1 ≤ N) (h2 : N < 2 ^ 30) : SeqDesign (sfr.e W N) "clk" := by
  sv_structure

end Examples.«system-verilog».seq_cycle.seq_refusals
