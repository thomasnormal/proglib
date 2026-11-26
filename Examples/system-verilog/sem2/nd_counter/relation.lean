import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleObl
import LeanModels.Sv.Known2
import LeanModels.Sv.Kernel.NdTrace

/-!
# A clocked counter over the relation: every trace is the fold of one function

```systemverilog
module nd_counter (input logic clk, input logic rst, input logic en, output logic [7:0] count);
  always_ff @(posedge clk) begin
    if (rst) count <= 8'd0;
    else if (en) count <= count + 8'd1;
  end
endmodule
```

The statements are about the choice-explicit relation of
`LeanModels/Sv/Kernel/NdStep.lean` (scheduling choice and per-read oracle
explicit, no fuel), on the design as loaded from its envelope, through the
multi-row closure `Nd.Trace`.

* `E_footprint`: the design passes the design-level non-interference test
  (`CoreMemDesign.NdFootprint`), decided by the kernel.
* `event_eq`: the design's event function (`CoreMemDesign.eventV`) is the
  obvious function `next` on the abstract state `St`.
* `counter_trace`: for EVERY stimulus (a list of input rows of any length,
  each row a real bit for `clk`, `rst`, `en`), every oracle and every
  schedule, the views of every trace are the running fold of `next`.
* `counter_count`: the value of `count` after the `k`-th row is the fold of
  `next` over the first `k + 1` rows.
* `counter_trace_exists`, `start_exists`: such traces and start stores exist.
* `counter_known_stays_known`: an invariant proved with the trace principle
  (`trace_invariant`): once `count` is known it is known after every row.

Start hypotheses, stated in every theorem: the store is coherent and its
scalar view is `abs a`: `clk` is a KNOWN bit (the relation refuses an x on a
clock; open owner question, interim option: control signals known), `rst` and
`en` hold any four-state value, and `count` is either all x (the power-on
value) or a known 8-bit value.  Every input row binds `clk`, `rst` and `en`
to real bits (environment inputs are real bits).  Interim options of the
other open owner questions: inputs-first within a row (the `rst` and `en` an
edge samples are the ones of the row that raises the clock), atomic
nonblocking commit, node-level granularity with the functional event derived
under the footprint test.

No simulator was run for this file; no oracle result is claimed.
-/

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».sem2.nd_counter

load_design_sv2 cnt from "Examples/system-verilog/sem2/nd_counter/nd_counter.sv.json"

def E : CoreMemDesign := match cnt.e with | .ok d => d | _ => default

set_option maxRecDepth 100000

theorem E_ok : cnt.e = .ok E := by rfl

/-- **The design passes the design-level non-interference test.** -/
theorem E_footprint : E.NdFootprint := { ok := by decide, edgeBase := by rfl }

/-! ## The abstract state and the obvious function -/

def vec1 (l : Logic) : LVec := ⟨#[l]⟩

/-- The scalar view with the given values. -/
def V (c : Bool) (r e : Logic) (n : LVec) : SvState :=
  [("clk", vec1 (Logic.ofBool c)), ("rst", vec1 r), ("en", vec1 e), ("count", n)]

/-- One input row: real bits for `clk`, `rst`, `en`. -/
def row (i : Bool × Bool × Bool) : SvState :=
  [("clk", vec1 (Logic.ofBool i.1)), ("rst", vec1 (Logic.ofBool i.2.1)),
   ("en", vec1 (Logic.ofBool i.2.2))]

/-- The abstract state: the clock bit, the last `rst` and `en` values, and
`count`: `none` is the all-x power-on value, `some x` a known value. -/
structure St where
  clk : Bool
  rst : Logic
  en : Logic
  count : Option (BitVec 8)

def cv : Option (BitVec 8) → LVec
  | none => LVec.xVec 8
  | some x => LVec.ofBitVec x

def abs (a : St) : SvState := V a.clk a.rst a.en (cv a.count)

/-- **The obvious function.**  The inputs are taken; on a rising clock the
counter resets when `rst`, else counts when `en`, else holds. -/
def next (a : St) (i : Bool × Bool × Bool) : St :=
  { clk := i.1
    rst := Logic.ofBool i.2.1
    en := Logic.ofBool i.2.2
    count :=
      if !a.clk && i.1 then
        if i.2.1 then some 0 else if i.2.2 then a.count.map (· + 1) else a.count
      else a.count }

/-! ## The design's event function is `next` -/

def zero8 : LVec := ⟨#[.l0, .l0, .l0, .l0, .l0, .l0, .l0, .l0]⟩
def one8 : LVec := ⟨#[.l1, .l0, .l0, .l0, .l0, .l0, .l0, .l0]⟩

def body : PStmt :=
  .block [.ifStmt (.ident "rst") (.nbaAssign "count" (.lit zero8))
    (some (.ifStmt (.ident "en")
      (.nbaAssign "count" (.binary (.m0 .add) (.ident "count") (.lit one8))) none))]

theorem E_procs : E.processes.toList = [.edge { clock := "clk", body := body }] := by rfl

/-- What the body issues on a view whose `rst` and `en` are real bits. -/
theorem solo_body (c r e : Bool) (n : LVec) :
    E.soloV E.env (V c (Logic.ofBool r) (Logic.ofBool e) n) memNone body =
      some (if r then [("count", 0, zero8)]
        else if e then [("count", 0, evalBinOp .add n one8)] else []) := by
  have hT : E.scalarTarget "count" = some 8 := by rfl
  have h1 : instExpr2 E.env (E.widthsOf E.elems) (some 1) (.ident "rst") = Expr2.ident "rst" := by
    simp
  have h2 : instExpr2 E.env (E.widthsOf E.elems) (some 1) (.ident "en") = Expr2.ident "en" := by
    simp
  have h3 : instExpr2 E.env (E.widthsOf E.elems) (some 8) (.lit zero8) = Expr2.lit zero8 := by
    simp
  have h4 : instExpr2 E.env (E.widthsOf E.elems) (some 8)
      (.binary (.m0 .add) (.ident "count") (.lit one8)) =
      Expr2.binary .add (.ident "count") (.lit one8) := by
    simp (config := { decide := true }) [instExpr2, ctxOpWidth2, rigidMax2, selfWidth2, fitExpr2,
      rigidExpr, PExpr.ctxPropagates, PExpr.constLeaf, PExpr.negGenvarWidened, PExpr.signedCast,
      CoreMemDesign.widthsOf, List.lookup]
    rfl
  have hm : LeanModels.Sv.PExpr.hasMemoryRead
      (.binary (.m0 .add) (.ident "count") (.lit one8)) = false := by
    first | rfl | decide | simp [LeanModels.Sv.PExpr.hasMemoryRead]
  have e1 : evalPure2 (V c (Logic.ofBool r) (Logic.ofBool e) n) (.ident "rst") =
      .ok (vec1 (Logic.ofBool r)) := by rfl
  have e2 : evalPure2 (V c (Logic.ofBool r) (Logic.ofBool e) n) (.ident "en") =
      .ok (vec1 (Logic.ofBool e)) := by rfl
  have e3 : evalPure2 (V c (Logic.ofBool r) (Logic.ofBool e) n)
      (.binary .add (.ident "count") (.lit one8)) = .ok (evalBinOp .add n one8) := by rfl
  simp only [body, CoreMemDesign.soloV, CoreMemDesign.soloListV, CoreMemDesign.soloOptV,
    CoreMemDesign.soloLeafV, hT, CoreMemDesign.evalV, CoreMemDesign.evalScalarV, h1, h2, h3,
    h4, hm, e1, e2, e3, evalPure2_lit]
  cases r <;> cases e <;> simp [vec1, LVec.condTrue, Logic.isKnown]

theorem fires_eq (c c' : Bool) (r e r' e' : Logic) (n : LVec) :
    CoreMemEdge.fires { clock := "clk", body := body } (V c r e n) (V c' r' e' n) =
      (!c && c') := by
  cases c <;> cases c' <;> rfl

/-- The updates of one event. -/
theorem queue_eq (c : Bool) (r e : Logic) (n : LVec) (i : Bool × Bool × Bool) :
    E.eventQueueV (V c r e n) (row i) =
      some (if !c && i.1 then
        (if i.2.1 then [("count", 0, zero8)]
          else if i.2.2 then [("count", 0, evalBinOp .add n one8)] else [])
        else []) := by
  obtain ⟨c', r', e'⟩ := i
  have hin : applyInputs2 E.scalar.toDesign2 (row (c', r', e')) (V c r e n) =
      V c' (Logic.ofBool r') (Logic.ofBool e') n := by rfl
  have hty : E.scalar.toDesign2.entryTypedB (row (c', r', e')) = true := by
    cases c' <;> cases r' <;> cases e' <;> rfl
  have hk : E.ndControlsKnownIn (V c r e n) = true := by cases c <;> rfl
  have hk' : E.ndControlsKnownIn (V c' (Logic.ofBool r') (Logic.ofBool e') n) = true := by
    cases c' <;> rfl
  unfold CoreMemDesign.eventQueueV
  rw [hin, hty, hk, hk', E_procs]
  cases c <;> cases c' <;>
    simp only [Bool.and_self, ↓reduceIte, CoreMemDesign.wakeQueueV, CoreMemProc.wakeBody?,
      fires_eq, solo_body, Bool.not_true, Bool.not_false, Bool.and_true, Bool.and_false,
      Bool.false_eq_true, List.append_nil]

theorem input_eq (c : Bool) (r e : Logic) (n : LVec) (i : Bool × Bool × Bool) :
    applyInputs2 E.scalar.toDesign2 (row i) (V c r e n) =
      V i.1 (Logic.ofBool i.2.1) (Logic.ofBool i.2.2) n := by rfl

theorem commit_count (c : Bool) (r e : Logic) (n x : LVec) :
    commitNba2 (V c r e n) [("count", 0, x)] = V c r e (n.insertAt 0 x) := by rfl

theorem add_x : evalBinOp .add (LVec.xVec 8) one8 = LVec.xVec 8 := by
  have hx : LVec.xVec 8 = ⟨#[.lx, .lx, .lx, .lx, .lx, .lx, .lx, .lx]⟩ := by rfl
  have h : (LVec.xVec 8).toNat? = none := by
    rw [hx]
    simp [LVec.toNat?, LVec.allKnown, Logic.isKnown]
  simp only [evalBinOp, LVec.add, h]
  rfl

theorem one8_eq : one8 = LVec.ofBitVec (1#8) := by decide

theorem zero8_eq : zero8 = LVec.ofBitVec (0#8) := by decide

theorem add_known (x : BitVec 8) :
    evalBinOp .add (LVec.ofBitVec x) one8 = LVec.ofBitVec (x + 1) := by
  rw [one8_eq]
  exact LVec.add_ofBitVec x 1

theorem cv_width (n : Option (BitVec 8)) : (cv n).width = 8 := by
  cases n with
  | none => rfl
  | some x => exact LVec.width_ofBitVec x

/-- **The design's event function is the obvious function**, on every
abstract state and every input row. -/
theorem event_eq (a : St) (i : Bool × Bool × Bool) :
    E.eventV (abs a) (row i) = some (abs (next a i)) := by
  obtain ⟨c, r, e, n⟩ := a
  obtain ⟨c', r', e'⟩ := i
  simp only [CoreMemDesign.eventV, abs, queue_eq, input_eq, Option.map_some, next]
  congr 1
  cases c <;> cases c' <;> cases r' <;> cases e' <;>
    simp only [Bool.not_true, Bool.not_false, Bool.and_true, Bool.and_false, Bool.false_eq_true,
      ↓reduceIte, commitNba2_nil, commit_count]
  · rw [LVec.insertAt_zero_of_width_eq]
    · cases n with
      | none => simp only [cv, Option.map_none, add_x]
      | some x => simp only [cv, Option.map_some, add_known]
    · cases n with
      | none => simp only [cv, add_x]
      | some x => simp only [cv, add_known, LVec.width_ofBitVec]
  · rw [LVec.insertAt_zero_of_width_eq (by rw [cv_width]; rfl)]
    simp only [cv, zero8_eq]
    rfl
  · rw [LVec.insertAt_zero_of_width_eq (by rw [cv_width]; rfl)]
    simp only [cv, zero8_eq]
    rfl

/-! ## The acceptance theorems -/

/-- **Every trace is the fold of the obvious function.**  From every coherent
store whose view is `abs a`, for every stimulus `ins` (any length), every
oracle and every schedule: the views of the stores of every trace of the
relation are `abs` of the running fold of `next`.  No bound on the number of
rows; no fuel. -/
theorem counter_trace (st : CoreMemState) (hc : E.Coherent st) (a : St)
    (hview : E.scalar.view st.scalar = abs a) (ins : List (Bool × Bool × Bool))
    (o o' : Oracle) (out : List CoreMemState) (ht : Nd.Trace E st o (ins.map row) out o') :
    out.map (fun s => E.scalar.view s.scalar) = (Nd.scan next a ins).map abs :=
  E_footprint.trace_refines event_eq ins st a o o' out hc hview ht

/-- **`count` after any row sequence is the fold of the obvious function.**
After the `k`-th row of any trace over any stimulus, `count` holds the value
the fold of `next` over the first `k + 1` rows gives. -/
theorem counter_count (st : CoreMemState) (hc : E.Coherent st) (a : St)
    (hview : E.scalar.view st.scalar = abs a) (ins : List (Bool × Bool × Bool))
    (o o' : Oracle) (out : List CoreMemState) (ht : Nd.Trace E st o (ins.map row) out o')
    (k : Nat) (hk : k < ins.length) :
    (out[k]?).map (fun s => SvState.lookup (E.scalar.view s.scalar) "count") =
      some (some (cv ((ins.take (k + 1)).foldl next a).count)) := by
  have h := E_footprint.trace_refines_at event_eq hc hview ht hk
  cases hout : out[k]? with
  | none => simp [hout] at h
  | some s =>
      simp only [hout, Option.map_some, Option.some.injEq] at h ⊢
      rw [h]
      rfl

/-- **A trace exists** for every stimulus and every oracle. -/
theorem counter_trace_exists (st : CoreMemState) (hc : E.Coherent st) (a : St)
    (hview : E.scalar.view st.scalar = abs a) (ins : List (Bool × Bool × Bool)) (o : Oracle) :
    ∃ out o', Nd.Trace E st o (ins.map row) out o' :=
  E_footprint.trace_exists event_eq ins st a o hc hview

/-- **The start hypotheses are satisfiable**: for every known clock bit and
all four-state values of `rst` and `en` there is a coherent store whose
`count` is the all-x power-on value. -/
theorem start_exists (c : Bool) (r e : Logic) :
    ∃ st, E.Coherent st ∧ E.scalar.view st.scalar = abs ⟨c, r, e, none⟩ := by
  refine ⟨E.normalizeScalar E.initial (E.storeFromView (abs ⟨c, r, e, none⟩)),
    E.normalizeScalar_coherent _ (E.typed_storeFromView _), ?_⟩
  rw [CoreMemDesign.normalizeScalar_view, CoreMemDesign.view_storeFromView]
  cases c <;> cases r <;> cases e <;> rfl

/-- An instance of the fold: from the power-on value, a rising edge with
`rst`, then three rising edges with `en`, leaves `count = 3`. -/
theorem fold_instance (c : Bool) (r e : Logic) :
    ([(false, true, false), (true, true, false), (false, false, true), (true, false, true),
      (false, false, true), (true, false, true), (false, false, true),
      (true, false, true)].foldl next ⟨c, r, e, none⟩).count = some 3 := by
  cases c <;> rfl

/-- **An invariant, by the trace principle.**  Once `count` is known it is
known after every row: for every stimulus, every oracle, every schedule. -/
theorem counter_known_stays_known (st : CoreMemState) (hc : E.Coherent st) (a : St)
    (hview : E.scalar.view st.scalar = abs a) (hknown : a.count.isSome = true)
    (ins : List (Bool × Bool × Bool)) (o o' : Oracle) (out : List CoreMemState)
    (ht : Nd.Trace E st o (ins.map row) out o') :
    ∀ s ∈ out, ∃ b : St, E.scalar.view s.scalar = abs b ∧ b.count.isSome = true := by
  refine E_footprint.trace_invariant
    (I := fun v => ∃ b : St, v = abs b ∧ b.count.isSome = true)
    (R := fun r => ∃ i, r = row i) ?_ hc ⟨a, hview, hknown⟩ ?_ ht
  · rintro v r ⟨b, rfl, hb⟩ ⟨i, rfl⟩
    refine ⟨_, event_eq b i, next b i, rfl, ?_⟩
    obtain ⟨c, r, e, n⟩ := b
    obtain ⟨c', r', e'⟩ := i
    cases n with
    | none => simp at hb
    | some x => cases c <;> cases c' <;> cases r' <;> cases e' <;> rfl
  · intro r hr
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hr
    exact ⟨i, rfl⟩

#print axioms E_footprint
#print axioms event_eq
#print axioms counter_trace
#print axioms counter_count
#print axioms counter_trace_exists
#print axioms start_exists
#print axioms fold_instance
#print axioms counter_known_stays_known

end Examples.«system-verilog».sem2.nd_counter
