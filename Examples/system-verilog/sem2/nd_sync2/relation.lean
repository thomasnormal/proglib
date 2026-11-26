import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleObl
import LeanModels.Sv.Known2
import LeanModels.Sv.Kernel.NdTrace

/-!
# The two-flop synchroniser with an asynchronous input, over the relation

```systemverilog
module nd_sync2 (input logic clk, input logic d, output logic s1, output logic s2);
  always_ff @(posedge clk) s1 <= d;
  always_ff @(posedge clk) s2 <= s1;
endmodule
```

**What this is, and what it is not.**  This is the E-layer statement: the
language-level meaning of the two processes under the relation of
`LeanModels/Sv/Kernel/NdStep.lean`.  THE MODEL HAS NO METASTABILITY: a flop
that samples `d` gets the value `d` holds, a real bit.  Nothing here says that
a physical synchroniser resolves, or bounds a failure rate; that belongs to
the hardware layer, which is not modelled.

The statement is NOT determinism.  It is functional correctness of the two
stages against an environment that is not synchronised to the clock: `d` is
an arbitrary real bit in EVERY input row (it may change with the clock edge,
between edges, or not at all), and the output two stages later is the value
`d` had in the row that raised the clock.

* `event_eq`: the design's event function is `next`: the inputs are taken;
  on a rising clock `s1` takes `d` and `s2` takes the old `s1`.
* `sync_trace`: for every stimulus (any list of rows, each a known `clk` bit
  and a real `d` bit; the clock need not alternate), every oracle and every
  schedule, the views of every trace are the running fold of `next`.
* `sync_two_stage`: under the clocking `cyc` (each cycle: a row with `clk`
  low, then a row with `clk` high; `d` free in both rows), `s2` after the
  rising row of cycle `k + 1` is the `d` of the rising row of cycle `k`.
* `sync_output`: the same value is what a reader sees in cycle `k + 2` before
  that cycle's edge (after its low row): the output in cycle `k + 2` equals
  the input sampled at the edge of cycle `k`.
* `sync_trace_exists`, `start_exists`: traces and start stores exist.

**Inputs-first is what fixes "the input sampled at the edge".**  The row that
raises `clk` may also change `d`.  Under the library's interim convention the
inputs of a row are applied first and the processes the row wakes then read
the store (open owner question "inputs-first within a row").  So the value
`s1` samples at an edge is the `d` OF THE RISING ROW.  Under the other
convention (processes read the store before the row's data inputs) the
sampled value would be the `d` of the previous row, and `sync_two_stage`
would be stated with that value.

Start hypotheses, in every theorem: a coherent store whose view is `abs a`:
`clk` is a KNOWN bit (the relation refuses x on a clock; interim option of
the open owner question: control signals known) and `d`, `s1`, `s2` hold any
four-state value, x included (the power-on value).  No bound on the number of
rows; no fuel.  Other interim options: atomic nonblocking commit; node-level
granularity, the functional event derived under the footprint test.

No simulator was run for this file; no oracle result is claimed.
-/

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».sem2.nd_sync2

load_design_sv2 sync from "Examples/system-verilog/sem2/nd_sync2/nd_sync2.sv.json"

def E : CoreMemDesign := match sync.e with | .ok d => d | _ => default

set_option maxRecDepth 100000

theorem E_ok : sync.e = .ok E := by rfl

/-- **The design passes the design-level non-interference test.** -/
theorem E_footprint : E.NdFootprint := { ok := by decide, edgeBase := by rfl }

/-! ## The abstract state and the function of one row -/

def vec1 (l : Logic) : LVec := ⟨#[l]⟩

/-- The scalar view with the given values. -/
def V (c : Bool) (d s1 s2 : Logic) : SvState :=
  [("clk", vec1 (Logic.ofBool c)), ("d", vec1 d), ("s1", vec1 s1), ("s2", vec1 s2)]

/-- One input row: a known clock bit and a real bit for the asynchronous
input `d`. -/
def row (i : Bool × Bool) : SvState :=
  [("clk", vec1 (Logic.ofBool i.1)), ("d", vec1 (Logic.ofBool i.2))]

/-- The abstract state: the clock bit and the four-state values of `d`, `s1`,
`s2`. -/
structure St where
  clk : Bool
  d : Logic
  s1 : Logic
  s2 : Logic

def abs (a : St) : SvState := V a.clk a.d a.s1 a.s2

/-- **The function of one row.**  The inputs are taken; on a rising clock
`s1` takes the `d` of this row and `s2` takes the old `s1`. -/
def next (a : St) (i : Bool × Bool) : St :=
  { clk := i.1
    d := Logic.ofBool i.2
    s1 := if !a.clk && i.1 then Logic.ofBool i.2 else a.s1
    s2 := if !a.clk && i.1 then a.s1 else a.s2 }

/-! ## The design's event function is `next` -/

theorem E_procs : E.processes.toList =
    [.edge { clock := "clk", body := .nbaAssign "s1" (.ident "d") },
     .edge { clock := "clk", body := .nbaAssign "s2" (.ident "s1") }] := by rfl

theorem soloV_s1 (c : Bool) (d s1 s2 : Logic) :
    E.soloV E.env (V c d s1 s2) memNone (.nbaAssign "s1" (.ident "d")) =
      some [("s1", 0, vec1 d)] := by
  have h1 : E.scalarTarget "s1" = some 1 := by rfl
  have h2 : instExpr2 E.env (E.widthsOf E.elems) (some 1) (.ident "d") = Expr2.ident "d" := by simp
  simp only [CoreMemDesign.soloV, CoreMemDesign.soloLeafV, h1, CoreMemDesign.evalV,
    CoreMemDesign.evalScalarV, h2]
  rfl

theorem soloV_s2 (c : Bool) (d s1 s2 : Logic) :
    E.soloV E.env (V c d s1 s2) memNone (.nbaAssign "s2" (.ident "s1")) =
      some [("s2", 0, vec1 s1)] := by
  have h1 : E.scalarTarget "s2" = some 1 := by rfl
  have h2 : instExpr2 E.env (E.widthsOf E.elems) (some 1) (.ident "s1") = Expr2.ident "s1" := by
    simp
  simp only [CoreMemDesign.soloV, CoreMemDesign.soloLeafV, h1, CoreMemDesign.evalV,
    CoreMemDesign.evalScalarV, h2]
  rfl

theorem fires_eq (body : PStmt) (c c' : Bool) (d s1 s2 d' : Logic) :
    CoreMemEdge.fires { clock := "clk", body := body } (V c d s1 s2) (V c' d' s1 s2) =
      (!c && c') := by
  cases c <;> cases c' <;> rfl

theorem event_V (c c' d' : Bool) (d s1 s2 : Logic) :
    E.eventV (V c d s1 s2) (row (c', d')) =
      some (V c' (Logic.ofBool d') (if !c && c' then Logic.ofBool d' else s1)
        (if !c && c' then s1 else s2)) := by
  have hin : applyInputs2 E.scalar.toDesign2 (row (c', d')) (V c d s1 s2) =
      V c' (Logic.ofBool d') s1 s2 := by rfl
  have hty : E.scalar.toDesign2.entryTypedB (row (c', d')) = true := by
    cases c' <;> cases d' <;> rfl
  have hk : E.ndControlsKnownIn (V c d s1 s2) = true := by cases c <;> rfl
  have hk' : E.ndControlsKnownIn (V c' (Logic.ofBool d') s1 s2) = true := by cases c' <;> rfl
  unfold CoreMemDesign.eventV CoreMemDesign.eventQueueV
  simp only [hin, hty, hk, hk', E_procs, Bool.and_self, ↓reduceIte]
  cases c <;> cases c' <;>
    simp only [CoreMemDesign.wakeQueueV, CoreMemProc.wakeBody?,
      fires_eq, soloV_s1, soloV_s2, Bool.not_true, Bool.not_false, Bool.and_true, Bool.and_false,
      Bool.false_eq_true, ↓reduceIte, Option.map_some] <;> rfl

/-- **The design's event function is `next`**, on every abstract state and
every input row. -/
theorem event_eq (a : St) (i : Bool × Bool) :
    E.eventV (abs a) (row i) = some (abs (next a i)) := by
  obtain ⟨c, d, s1, s2⟩ := a
  obtain ⟨c', d'⟩ := i
  exact event_V c c' d' d s1 s2

/-! ## Every trace is the fold of `next` -/

/-- **Every trace is the fold of `next`.**  From every coherent store whose
view is `abs a`, for every stimulus (any length; `clk` any known bit per row,
`d` any real bit per row), every oracle and every schedule. -/
theorem sync_trace (st : CoreMemState) (hc : E.Coherent st) (a : St)
    (hview : E.scalar.view st.scalar = abs a) (ins : List (Bool × Bool))
    (o o' : Oracle) (out : List CoreMemState) (ht : Nd.Trace E st o (ins.map row) out o') :
    out.map (fun s => E.scalar.view s.scalar) = (Nd.scan next a ins).map abs :=
  E_footprint.trace_refines event_eq ins st a o o' out hc hview ht

/-- **A trace exists** for every stimulus and every oracle. -/
theorem sync_trace_exists (st : CoreMemState) (hc : E.Coherent st) (a : St)
    (hview : E.scalar.view st.scalar = abs a) (ins : List (Bool × Bool)) (o : Oracle) :
    ∃ out o', Nd.Trace E st o (ins.map row) out o' :=
  E_footprint.trace_exists event_eq ins st a o hc hview

/-- **The start hypotheses are satisfiable**: for every known clock bit and
all four-state values of `d`, `s1`, `s2` (x included) there is a coherent
store with that view. -/
theorem start_exists (a : St) : ∃ st, E.Coherent st ∧ E.scalar.view st.scalar = abs a := by
  obtain ⟨c, d, s1, s2⟩ := a
  refine ⟨E.normalizeScalar E.initial (E.storeFromView (abs ⟨c, d, s1, s2⟩)),
    E.normalizeScalar_coherent _ (E.typed_storeFromView _), ?_⟩
  rw [CoreMemDesign.normalizeScalar_view, CoreMemDesign.view_storeFromView]
  cases c <;> cases d <;> cases s1 <;> cases s2 <;> rfl

/-! ## The clocked stimulus, and the two stages -/

/-- The clocking: each cycle is a row with the clock low and a row with the
clock high.  `p.1` is the value of `d` in the low row, `p.2` its value in the
row that raises the clock.  Both are free. -/
def cyc : List (Bool × Bool) → List (Bool × Bool)
  | [] => []
  | p :: ps => (false, p.1) :: (true, p.2) :: cyc ps

/-- One cycle, as a function: `s1` takes the `d` of the rising row, `s2` the
old `s1`. -/
def cstep (a : St) (p : Bool × Bool) : St :=
  { clk := true, d := Logic.ofBool p.2, s1 := Logic.ofBool p.2, s2 := a.s1 }

theorem next_cycle (a : St) (p : Bool × Bool) :
    next (next a (false, p.1)) (true, p.2) = cstep a p := by
  obtain ⟨c, d, s1, s2⟩ := a
  cases c <;> rfl

theorem next_low_s2 (a : St) (x : Bool) : (next a (false, x)).s2 = a.s2 := by
  simp [next]

theorem fold_cyc : ∀ (ds : List (Bool × Bool)) (a : St),
    (cyc ds).foldl next a = ds.foldl cstep a
  | [], _ => rfl
  | p :: ps, a => by
      simp only [cyc, List.foldl_cons, next_cycle, fold_cyc ps]

theorem cyc_length : ∀ ds : List (Bool × Bool), (cyc ds).length = 2 * ds.length
  | [] => rfl
  | p :: ps => by simp [cyc, cyc_length ps]; omega

theorem cyc_take : ∀ (m : Nat) (ds : List (Bool × Bool)),
    (cyc ds).take (2 * m) = cyc (ds.take m)
  | 0, _ => by simp [cyc]
  | m + 1, [] => by simp [cyc]
  | m + 1, p :: ps => by
      have h : 2 * (m + 1) = 2 * m + 1 + 1 := by omega
      rw [h]
      simp only [cyc, List.take_succ_cons, cyc_take m ps]

theorem cyc_take_succ : ∀ (m : Nat) (ds : List (Bool × Bool)) (p : Bool × Bool),
    ds[m]? = some p → (cyc ds).take (2 * m + 1) = cyc (ds.take m) ++ [(false, p.1)]
  | _, [], _, h => by simp at h
  | 0, q :: ps, p, h => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      simp [cyc]
  | m + 1, q :: ps, p, h => by
      have hm : 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 := by omega
      simp only [List.getElem?_cons_succ] at h
      rw [hm]
      simp only [cyc, List.take_succ_cons, cyc_take_succ m ps p h, List.cons_append]

/-- The two stages, on the abstract function: after `k + 2` cycles `s2` holds
the `d` of the rising row of cycle `k`. -/
theorem two_stage : ∀ (k : Nat) (ds : List (Bool × Bool)) (a : St) (p : Bool × Bool),
    ds[k]? = some p → k + 1 < ds.length →
      ((ds.take (k + 2)).foldl cstep a).s2 = Logic.ofBool p.2
  | _, [], _, _, h, _ => by simp at h
  | 0, [q], _, _, _, hl => by simp at hl
  | 0, q :: q' :: ps, a, p, h, _ => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      rfl
  | k + 1, q :: ps, a, p, h, hl => by
      simp only [List.getElem?_cons_succ] at h
      have := two_stage k ps (cstep a q) p h (by simpa using hl)
      simpa [List.take_succ_cons] using this

/-- **The two stages are correct, for an asynchronous input.**  From every
coherent store whose view is `abs a`, for every list of cycles `ds` (any
length; `d` an arbitrary real bit in the low row and in the rising row of
every cycle), every oracle and every schedule: in every trace of the
relation, after the rising row of cycle `k + 1` the output `s2` holds the
value `d` had in the row that raised the clock in cycle `k`.

That the sampled value is the `d` of the rising row itself is the library's
interim inputs-first convention (see the file header). -/
theorem sync_two_stage (st : CoreMemState) (hc : E.Coherent st) (a : St)
    (hview : E.scalar.view st.scalar = abs a) (ds : List (Bool × Bool))
    (o o' : Oracle) (out : List CoreMemState)
    (ht : Nd.Trace E st o ((cyc ds).map row) out o')
    (k : Nat) (p : Bool × Bool) (hp : ds[k]? = some p) (hk : k + 1 < ds.length) :
    (out[2 * (k + 1) + 1]?).map (fun s => SvState.lookup (E.scalar.view s.scalar) "s2") =
      some (some (vec1 (Logic.ofBool p.2))) := by
  have hlen : 2 * (k + 1) + 1 < (cyc ds).length := by rw [cyc_length]; omega
  have h := E_footprint.trace_refines_at event_eq hc hview ht hlen
  have hidx : 2 * (k + 1) + 1 + 1 = 2 * (k + 2) := by omega
  rw [hidx, cyc_take, fold_cyc] at h
  cases hout : out[2 * (k + 1) + 1]? with
  | none => simp [hout] at h
  | some s =>
      simp only [hout, Option.map_some, Option.some.injEq] at h ⊢
      rw [h]
      show some (vec1 ((ds.take (k + 2)).foldl cstep a).s2) = _
      rw [two_stage k ds a p hp hk]

/-- **The output in cycle `k + 2` equals the input sampled at the edge of
cycle `k`.**  The same hypotheses; `s2` read in cycle `k + 2` before that
cycle's rising row (after its low row) is the value `d` had in the row that
raised the clock in cycle `k`.  No bound on `k` or on the number of cycles. -/
theorem sync_output (st : CoreMemState) (hc : E.Coherent st) (a : St)
    (hview : E.scalar.view st.scalar = abs a) (ds : List (Bool × Bool))
    (o o' : Oracle) (out : List CoreMemState)
    (ht : Nd.Trace E st o ((cyc ds).map row) out o')
    (k : Nat) (p : Bool × Bool) (hp : ds[k]? = some p) (hk : k + 2 < ds.length) :
    (out[2 * (k + 2)]?).map (fun s => SvState.lookup (E.scalar.view s.scalar) "s2") =
      some (some (vec1 (Logic.ofBool p.2))) := by
  have hlen : 2 * (k + 2) < (cyc ds).length := by rw [cyc_length]; omega
  have h := E_footprint.trace_refines_at event_eq hc hview ht hlen
  obtain ⟨q, hq⟩ : ∃ q, ds[k + 2]? = some q := ⟨ds[k + 2], List.getElem?_eq_getElem hk⟩
  rw [cyc_take_succ (k + 2) ds q hq, List.foldl_append, fold_cyc] at h
  cases hout : out[2 * (k + 2)]? with
  | none => simp [hout] at h
  | some s =>
      simp only [hout, Option.map_some, Option.some.injEq] at h ⊢
      rw [h]
      show some (vec1 (next ((ds.take (k + 2)).foldl cstep a) (false, q.1)).s2) = _
      rw [next_low_s2, two_stage k ds a p hp (by omega)]

/-- An instance: three cycles whose rising rows carry `d = 1, 0, 1`; the
output read in the third cycle is the first sample. -/
theorem fold_instance (a : St) :
    ((cyc [(false, true), (true, false), (false, true)]).take 5 |>.foldl next a).s2 = .l1 := by
  obtain ⟨c, d, s1, s2⟩ := a
  cases c <;> rfl

#print axioms E_footprint
#print axioms event_eq
#print axioms sync_trace
#print axioms sync_trace_exists
#print axioms start_exists
#print axioms two_stage
#print axioms sync_two_stage
#print axioms sync_output
#print axioms fold_instance

end Examples.«system-verilog».sem2.nd_sync2
