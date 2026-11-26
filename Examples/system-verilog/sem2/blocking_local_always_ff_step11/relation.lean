import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.NdSound

/-!
# Blocking writes to a static local are in the fragment of the soundness theorem

```systemverilog
always_ff @(posedge clk) begin : capture
    logic [3:0] t;
    t = d;
    q <= t;
    t = ~t;
    q_not <= t;
end
```

An instance of `CoreMemDesign.step_sound` on a body with a declaration of a
static local and two BLOCKING assignments to it, between nonblocking
assignments that sample it.  `E_nbaClocked` is decided by the kernel on the
loaded design, and `E_body` shows the body the fragment test was run on.

What is and is not shown here: the design is in the fragment
`CoreMemDesign.NbaClocked`, and the two soundness theorems are instantiated
on it with their start hypotheses left visible (a typed store; the clock
known before the row and in the executor's result).  That the executor
returns on a row is EVALUATED by the `#guard` below (the compiled evaluator,
not the kernel), on one concrete row: `q` takes `d` and `q_not` takes `~d`,
each sampling the local between the two blocking writes.  No simulator was
run for this file; the simulator receipt of this directory is `check.py`.
-/

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».sem2.blocking_local_always_ff_step11.relation

load_design_sv2 blk from "Examples/system-verilog/sem2/blocking_local_always_ff_step11/blocking_local_always_ff_step11.sv.json"

def E : CoreMemDesign := match blk.e with | .ok d => d | _ => default

set_option maxRecDepth 100000

theorem E_ok : blk.e = .ok E := by rfl

/-- The clock is the only control signal. -/
theorem E_sources : E.ndEventSources = ["clk"] := by decide

/-- The body: a static local, two blocking writes to it, two nonblocking
samples of it. -/
theorem E_body : E.processes.toList =
    [.edge { clock := "clk",
             body := .block [.localDecl "t" 4 none,
               .blockingAssign "t" (.ident "d"),
               .nbaAssign "q" (.ident "t"),
               .blockingAssign "t" (.unary (.m0 .bnot) (.ident "t")),
               .nbaAssign "q_not" (.ident "t")] }] := by rfl

/-- The design is in the fragment: each field is decided by the kernel. -/
theorem E_nbaClocked : E.NbaClocked :=
  { admitted := by decide
    bodies := by decide
    fourState := by decide
    edgeBase := by rfl }

/-- `step_sound` on this design: from a typed store with `clk` known, an
executor result with `clk` known is the end of a settled run of the relation
under the executor's choices. -/
theorem blocking_step_sound (st next : CoreMemState) (entry : SvState)
    (hT : E.scalar.Typed st.scalar) (hk : E.ControlsKnown st)
    (h : E.step st entry = .ok next) (hk' : E.ControlsKnown next) :
    ∃ t, Nd.EventSettles E st entry Oracle.zero t ∧ t.store = next ∧ t.oracle = Oracle.zero :=
  CoreMemDesign.step_sound E_nbaClocked hT hk h hk'

/-- The row-list form on this design. -/
theorem blocking_rows_sound (rows : List SvState) (st : CoreMemState) (out : List CoreMemState)
    (hT : E.scalar.Typed st.scalar) (hk : E.ControlsKnown st)
    (hne : ∀ row ∈ rows, (row.isEmpty && E.scalarAssignInputsOnly) = false)
    (h : runCoreMemRows E st rows = .ok out) (hout : ∀ st' ∈ out, E.ControlsKnown st') :
    Nd.Trace E st Oracle.zero rows out Oracle.zero :=
  runCoreMemRows_sound E_nbaClocked rows st out hT hk hne h hout

/-! ## The executor returns on a row (evaluated, not kernel-checked) -/

/-- A start store: `clk = 0`, everything else x. -/
def start : CoreMemState :=
  E.normalizeScalar E.initial (E.storeFromView
    [("clk", ⟨#[.l0]⟩), ("d", LVec.xVec 4), ("q", LVec.xVec 4), ("q_not", LVec.xVec 4),
     ("t", LVec.xVec 4)])

/-- The clock rises with `d = 4'b1010` (bit 0 first). -/
def riseRow : SvState := [("clk", ⟨#[.l1]⟩), ("d", ⟨#[.l0, .l1, .l0, .l1]⟩)]

#guard decide (E.ControlsKnown start)

#guard match E.step start riseRow with
  | .ok next =>
      decide (E.ControlsKnown next) &&
        SvState.lookup (E.scalar.view next.scalar) "q" == some ⟨#[.l0, .l1, .l0, .l1]⟩ &&
        SvState.lookup (E.scalar.view next.scalar) "q_not" == some ⟨#[.l1, .l0, .l1, .l0]⟩ &&
        SvState.lookup (E.scalar.view next.scalar) "t" == some ⟨#[.l1, .l0, .l1, .l0]⟩
  | _ => false

#print axioms E_nbaClocked
#print axioms blocking_step_sound
#print axioms blocking_rows_sound

end Examples.«system-verilog».sem2.blocking_local_always_ff_step11.relation
