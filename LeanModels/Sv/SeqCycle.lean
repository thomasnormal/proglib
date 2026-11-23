import LeanModels.Sv.Kernel.CoreMemExec
import LeanModels.Sv.Kernel.Core0Obs
import LeanModels.Sv.Kernel.Core1Edge
import LeanModels.Sv.SeqCycleStep

/-!
# The clock cycle of the ordinary E route, derived (`LeanModels.Sv.Kernel`, the clocked tactics' theory)

**Status: derived from the ordinary E route** (the loader's `X.e`, `PDesign.instantiateE2`, and its slot function
`CoreMemDesign.step`). Nothing here is a semantics: every definition is a function of the route's own data, and every
theorem relates it to `CoreMemDesign.step`.

A design declares no clock: its EVENTS are computed (`CoreMemDesign.events`: each edge process's clock edge, rising or
falling, and its asynchronous reset's assertion edge; the route's `CoreMemEdge.fires` is "some event of the process
occurs"). A run is a list of rows; the input discipline `Separated` reads each as a DATA ROW (no event occurs) or an
INSTANT ROW (only event sources move, some event occurs, no process sees its clock event while its reset moves). The
INSTANT FUNCTION `tick` is the mirror's slot on an instant's row, `dataV` on a data row: one view, indexed by events.

Single clock is that view at the one event `posedge clk`: a clock cycle is a data row (the LOW slot: the cycle's data
inputs with the clock at 0, `lowEntry`) then the instant `{posedge clk}` (the HIGH slot, `highEntry` =
`(Instant.rise clk).row`). The pre sample is the state after the low slot, the post sample the state after the high
slot. An asynchronous reset is an event of its own: its fall in the low slot fires its processes there (§9.4.2), so the
pre sample already shows the reset; the discipline admits that low slot only when no data moves with it.

A clocked state on views is a pair: the scalar VIEW (the name-to-value list `evalPure2` reads) and the MEMORY VIEW
(`MemV`: each memory's contents as a function of its source label, the route's `MemBlock.read`). A memory is an indexed
family, never cells: its next contents are one write equation (`memWrite`), its reads one read equation (`memRd`), both
deciding x/z exactly as the route does (`MemShape.index?`: an x/z or out-of-range index reads x and writes nothing,
§11.5.1; the index and the value are sampled when the update is issued, §10.4.2).

* `CoreMemDesign.evalV`, `evalIdxV`, `evalListV`: the route's expression evaluator (`evalExprLocals`) on a view and a
  memory view; equal to it (`evalExprLocals_eq_evalV`) on a state whose memory is coherent (`MemCoherent`).
* `CoreMemDesign.execV`: the route's edge-body executor (`execStmtFuel`) on views: blocking and nonblocking writes to
  whole signals, selects and concatenations, nonblocking writes to memory elements, `if`, `case` (every mode, plain and
  qualified), blocks, and a procedural `for` loop of nonblocking writes: the fold of its body over the header's value
  list (`execLoopV` over the route's `forValues2`, the body under `env.bindVal iterator i`; the list is a function of
  the parameters and is never unrolled); `execStmtFuel_V`: the route's executor lands on its view and issues exactly
  its updates, at every fuel from the body's need on (`PStmt.need`: for a loop, `2 + trips + need body`). The normal
  entry point adds runtime fuel from the evaluated header, so the profile does not impose a trip-count bound.
* `memWriteL`: the write equation of a loop of element writes, over the header's value list; `memWriteL_at`,
  `memWriteL_index`, `memWriteL_id`, `memWriteL_of_not_key`: its cells in closed form.
* `CoreMemDesign.edgesV`: the route's edge pass on views, each process firing by `CoreMemEdge.fires` (the clock's rise or
  the asynchronous reset's fall, x/z rows included); `runEdges_V`.
* `CoreMemDesign.commitNba_V`: the route's commit of memory records is `commitMemV` on the memory view.
* `CoreMemProc.edge?`, `coreMemEventEdge?`, `CoreMemDesign.edgeProcs`: the edge processes of a design. A plain
  `always` whose event list is one clock edge with an optional asynchronous reset edge is one: the route fires it by the
  same edge table and runs the same body (`coreMemEventEdge?_spec`, `runEdges_event`; IEEE 1800-2017 §9.2.2.1, §9.2.2.4).
* `SeqProfileI E`: the clocked profile, any number of clocks: edge processes on either edge of any clock whose bodies
  `execV` mirrors, continuous assigns (a memory read evaluated by the route's evaluator, the rest compiled), one-rank
  4-state memories of distinct names that are not ports, no always_comb, always_latch, always @* or initial process,
  4-state declarations with distinct names. `SeqProfile E clk`: its single-clock instance (every edge process on the
  rising edge of `clk`).
* `SeqEvent`, `CoreMemDesign.events`, `occurs`; `Instant`, `DataRow`, `InstantRow`, `Separated`, `instOf`; `dataV`,
  `tick`: the instant view (its theorems in `SeqCycleInstant.lean`).
* `CoreMemDesign.Coherent`, `MemCoherent`: a state whose store is its cache's, one typed value per declaration; a memory
  state holding every memory's block under its identity.
* `CoreMemDesign.settleV`, `slotV`, `cycleMV`: the slot and the cycle on views: two continuous-assign passes, the edge
  round, the commit, two passes (the route's slot repeats its passes and its edge round until nothing changes; under the
  obligations both loops stop after their first round, `SeqCycleObl.lean`); `cycleMV` is `dataV` then
  `tick (Instant.rise clk)`; `cycleV`: the cycle of a design without memories (the scalar part of `cycleMV`).

The obligations, the theorems that use them and the refinement theorems (`CoreMemDesign.step_seq`, `cycleMV_refines`,
`cycle_of_seqProfile`: from every coherent state, the route's slots exist, stay coherent, and land exactly on the views
`cycleMV` computes) are in `SeqCycleObl.lean`, the runs and the run judgment in `SeqCycleRuns.lean`. The route's slot
function is read only through the interface lemmas of `SeqCycleStep.lean`.
-/


namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

/-! ## The clocking discipline's slot entries -/

/-- The low slot of a cycle: the cycle's data inputs, the clock at 0. -/
def lowEntry (clk : String) (data : SvState) : SvState := (clk, ⟨#[.l0]⟩) :: data

/-- The high slot of a cycle: the clock raised, nothing else changed. -/
def highEntry (clk : String) : SvState := [(clk, ⟨#[.l1]⟩)]

/-- The slot entries of a run of cycles, two per cycle. -/
def cycleRows (clk : String) : List SvState → List SvState
  | [] => []
  | d :: ds => lowEntry clk d :: highEntry clk :: cycleRows clk ds

/-! ## The memory view: one read equation, one write equation -/

/-- **The memory view**: each memory's contents by name and source label (the route's `MemBlock.read`, x outside the
declared range). -/
abbrev MemV := String → Int → LVec

/-- Memory nonblocking-update records on views: the memory's name, the resolved label, the value already converted to
the element type (§10.4.2: index and value sampled at issue). -/
abbrev MemQV := List (String × Int × LVec)

/-- The memory view of a design without memories (never read). -/
def memNone : MemV := fun _ _ => ⟨#[]⟩

/-- **The read equation**: the cell at the resolved label, or all x at the element width when the index was x/z or out
of range (§11.5.1). -/
def memRd (mv : MemV) (n : String) (k? : Option Int) (w : Nat) : LVec :=
  match k? with
  | some k => mv n k
  | none => LVec.xVec w

/-- The records one nonblocking write to a memory element issues: none when the index was x/z or out of range (the
no-op of §11.5.1). -/
def memIss (n : String) (k? : Option Int) (x : LVec) : MemQV :=
  match k? with
  | some k => [(n, k, x)]
  | none => []

/-- **The write equation**: the memory `n` written at the resolved label with `x`; every other cell and every other
memory unchanged; nothing written when the index was x/z or out of range. -/
def memWrite (mv : MemV) (n : String) (k? : Option Int) (x : LVec) : MemV :=
  fun n' k => if n' = n ∧ k? = some k then x else mv n' k

/-- The commit of memory records in issue order (a later record to the same cell wins, as `MemState.commitNba`). -/
def commitMemV (mv : MemV) : MemQV → MemV
  | [] => mv
  | (n, k, x) :: rest => commitMemV (memWrite mv n (some k) x) rest

/-- `MemBlock.readIndex` on the memory view: the read of an element at a run-time index. -/
def CoreMemDecl.readV (md : CoreMemDecl) (mv : MemV) (signed : Bool) (idx : LVec) : LVec :=
  memRd mv md.source.name (md.shape.index? signed idx) md.shape.elemWidth

/-- `MemState.issueNba` on the memory view: the records a nonblocking write to an element issues. -/
def CoreMemDecl.issueV (md : CoreMemDecl) (signed : Bool) (idx x : LVec) : MemQV :=
  memIss md.source.name (md.shape.index? signed idx) (md.shape.convert x)

@[simp] theorem commitMemV_nil (mv : MemV) : commitMemV mv [] = mv := rfl

theorem commitMemV_cons (mv : MemV) (u : String × Int × LVec) (q : MemQV) :
    commitMemV mv (u :: q) = commitMemV (memWrite mv u.1 (some u.2.1) u.2.2) q := by
  cases u
  rfl

theorem memWrite_comm_of_name_ne (mv : MemV) {n n' : String} {k k' : Int}
    {x x' : LVec} (h : n ≠ n') :
    memWrite (memWrite mv n (some k) x) n' (some k') x' =
      memWrite (memWrite mv n' (some k') x') n (some k) x := by
  funext name index
  by_cases hn : name = n
  · subst name
    simp [memWrite, h, Ne.symm h]
  · by_cases hn' : name = n'
    · subst name
      simp [memWrite, h, Ne.symm h]
    · simp [memWrite, h, Ne.symm h, hn, hn']

theorem commitMemV_move {u : String × Int × LVec} : ∀ {mv : MemV} {B R : MemQV},
    (∀ u' ∈ B, u.1 ≠ u'.1) →
      commitMemV mv (u :: (B ++ R)) = commitMemV mv (B ++ u :: R)
  | _, [], _, _ => rfl
  | mv, (n, k, x) :: B, R, h => by
      rw [List.cons_append, commitMemV_cons, commitMemV_cons]
      rw [memWrite_comm_of_name_ne _ (h (n, k, x) (List.mem_cons_self ..))]
      rw [← commitMemV_cons]
      exact commitMemV_move (fun u' hu' => h u' (List.mem_cons_of_mem _ hu'))

theorem commitMemV_swap : ∀ {mv : MemV} {q₁ q₂ : MemQV},
    (∀ u ∈ q₁, ∀ u' ∈ q₂, u.1 ≠ u'.1) →
      commitMemV mv (q₁ ++ q₂) = commitMemV mv (q₂ ++ q₁)
  | _, [], _, _ => by simp
  | mv, u :: q₁, q₂, h => by
      rw [List.cons_append, commitMemV_cons,
        commitMemV_swap
          (fun x hx y hy => h x (List.mem_cons_of_mem _ hx) y hy),
        ← commitMemV_cons]
      exact commitMemV_move (fun u' hu' => h u (List.mem_cons_self ..) u' hu')

theorem commitMemV_append (mv : MemV) : ∀ (q₁ q₂ : MemQV), commitMemV mv (q₁ ++ q₂) = commitMemV (commitMemV mv q₁) q₂
  | [], _ => rfl
  | (n, k, x) :: rest, q₂ => by
      show commitMemV (memWrite mv n (some k) x) (rest ++ q₂) = _
      rw [commitMemV_append]
      rfl

@[simp] theorem memWrite_none (mv : MemV) (n : String) (x : LVec) : memWrite mv n none x = mv := by
  funext n' k
  simp [memWrite]

/-- The commit of one issued write is the write equation. -/
theorem commitMemV_memIss (mv : MemV) (n : String) (k? : Option Int) (x : LVec) (q : MemQV) :
    commitMemV mv (memIss n k? x ++ q) = commitMemV (memWrite mv n k? x) q := by
  cases k? with
  | none => simp [memIss]
  | some k => rfl

/-- A read after a write: the written value at the written cell, the old contents elsewhere. -/
theorem memRd_memWrite (mv : MemV) (n n' : String) (k? k2? : Option Int) (x : LVec) (w : Nat) :
    memRd (memWrite mv n k? x) n' k2? w =
      if n' = n ∧ k2?.isSome = true ∧ k? = k2? then x else memRd mv n' k2? w := by
  cases k2? with
  | none => simp [memRd]
  | some k => simp [memRd, memWrite]

/-! ### The write equation of a loop

A procedural `for` loop of nonblocking element writes `m[a(i)] <= e(i)` issues one record per value of its header's
value list. Its commit is ONE equation, `memWriteL`, over that list (a function of the parameters: never unrolled):
the cell a value's key resolves to holds that value's data (`memWriteL_at`, when no other value of the list resolves to
the cell: an injective index), every other cell and every other memory is unchanged (`memWriteL_of_not_key`); for the
identity index `m[i] <= e(i)` that is `fun k => if k is a value of the list then e(k) else the old cell`
(`memWriteL_id`). Index and data are read before the loop's commit (§10.4.2: sampled at issue). -/

/-- **The write equation of a loop**: the memory `n` after the element writes a loop issues, in order: for each value
`i` of the list a write at the resolved label `key i` (none: no write, §11.5.1) of `x i`; a later write to the same
cell wins. The list is the loop header's value list. -/
def memWriteL (mv : MemV) (n : String) (vals : List Int) (key : Int → Option Int) (x : Int → LVec) : MemV :=
  commitMemV mv (vals.flatMap fun i => memIss n (key i) (x i))

/-- The commit of a loop's issued element writes is its write equation. -/
theorem commitMemV_flatMap_memIss (mv : MemV) (n : String) (vals : List Int) (key : Int → Option Int)
    (x : Int → LVec) : commitMemV mv (vals.flatMap fun i => memIss n (key i) (x i)) = memWriteL mv n vals key x := rfl

/-- The commit of a loop's issued element writes followed by further records. -/
theorem commitMemV_flatMap_memIss_append (mv : MemV) (n : String) (vals : List Int) (key : Int → Option Int)
    (x : Int → LVec) (q : MemQV) :
    commitMemV mv ((vals.flatMap fun i => memIss n (key i) (x i)) ++ q) =
      commitMemV (memWriteL mv n vals key x) q := by
  rw [commitMemV_append]
  rfl

@[simp] theorem memWriteL_nil (mv : MemV) (n : String) (key : Int → Option Int) (x : Int → LVec) :
    memWriteL mv n [] key x = mv := by
  simp [memWriteL]

/-- The write equation of a loop, one value at a time (a lemma about the list, not an unrolling of a design). -/
theorem memWriteL_cons (mv : MemV) (n : String) (i : Int) (vals : List Int) (key : Int → Option Int)
    (x : Int → LVec) :
    memWriteL mv n (i :: vals) key x = memWriteL (memWrite mv n (key i) (x i)) n vals key x := by
  unfold memWriteL
  rw [List.flatMap_cons, commitMemV_memIss]

/-- **A cell no value of the loop resolves to is unchanged** (another memory, or a label outside the loop's keys). -/
theorem memWriteL_of_not_key {n n' : String} {k : Int} {key : Int → Option Int} {x : Int → LVec} :
    ∀ (vals : List Int) (mv : MemV), (n' = n → ∀ i ∈ vals, key i ≠ some k) → memWriteL mv n vals key x n' k = mv n' k
  | [], mv, _ => by simp
  | i :: vals, mv, h => by
      rw [memWriteL_cons, memWriteL_of_not_key vals _ (fun hn j hj => h hn j (List.mem_cons_of_mem _ hj))]
      unfold memWrite
      rw [if_neg]
      rintro ⟨hn, hk⟩
      exact h hn i (by simp) hk

/-- **The cell a value of the loop resolves to holds that value's data**, when no other value of the list resolves to
the same cell (an injective index). -/
theorem memWriteL_at {n : String} {key : Int → Option Int} {x : Int → LVec} {k i : Int} :
    ∀ (vals : List Int) (mv : MemV), i ∈ vals → key i = some k → (∀ j ∈ vals, key j = some k → j = i) →
      memWriteL mv n vals key x n k = x i
  | [], _, hi, _, _ => by simp at hi
  | j :: vals, mv, hi, hk, hu => by
      rw [memWriteL_cons]
      by_cases hmem : i ∈ vals
      · exact memWriteL_at vals _ hmem hk (fun j' hj' h' => hu j' (List.mem_cons_of_mem _ hj') h')
      · have hji : j = i := by
          rcases List.mem_cons.mp hi with h | h
          · exact h.symm
          · exact absurd h hmem
        rw [memWriteL_of_not_key vals _ (fun _ j' hj' h' => hmem (by
          rw [← hu j' (List.mem_cons_of_mem _ hj') h']; exact hj'))]
        simp [memWrite, hji, hk]

/-- **The loop `m[f(i)] <= e(i)` with an injective index**: the cell `f i` of a value `i` of the list holds `e(i)`. -/
theorem memWriteL_index {n : String} {key : Int → Option Int} {x : Int → LVec} {vals : List Int} {f : Int → Int}
    (hkey : ∀ i ∈ vals, key i = some (f i)) (hinj : ∀ i ∈ vals, ∀ j ∈ vals, f i = f j → i = j) (mv : MemV)
    {i : Int} (hi : i ∈ vals) : memWriteL mv n vals key x n (f i) = x i :=
  memWriteL_at vals mv hi (hkey i hi) fun j hj h' => hinj j hj i hi (by
    rw [hkey j hj] at h'
    exact Option.some.inj h')

/-- **The loop `m[i] <= e(i)`** (every value of the list resolves to its own label): the memory `n` holds `e(k)` at
each value `k` of the list and its old contents elsewhere; every other memory is unchanged. -/
theorem memWriteL_id {n : String} {key : Int → Option Int} {x : Int → LVec} {vals : List Int}
    (hkey : ∀ i ∈ vals, key i = some i) (mv : MemV) (n' : String) (k : Int) :
    memWriteL mv n vals key x n' k = if n' = n ∧ k ∈ vals then x k else mv n' k := by
  by_cases h : n' = n ∧ k ∈ vals
  · obtain ⟨rfl, hk⟩ := h
    rw [if_pos ⟨rfl, hk⟩]
    exact memWriteL_at vals mv hk (hkey k hk) fun j hj h' => by
      rw [hkey j hj] at h'
      exact Option.some.inj h'
  · rw [if_neg h]
    exact memWriteL_of_not_key vals mv fun hn i hi h' => h ⟨hn, by
      rw [hkey i hi] at h'
      rw [← Option.some.inj h']
      exact hi⟩

/-- The elements of a memory a loop writes keep their width when every written value has it. -/
theorem memWriteL_width {n : String} {key : Int → Option Int} {x : Int → LVec} {w : Nat} :
    ∀ (vals : List Int) (mv : MemV), (∀ k, (mv n k).width = w) → (∀ i ∈ vals, (x i).width = w) →
      ∀ k, (memWriteL mv n vals key x n k).width = w
  | [], mv, hmv, _, k => by simpa using hmv k
  | i :: vals, mv, hmv, hx, k => by
      rw [memWriteL_cons]
      refine memWriteL_width vals _ (fun k' => ?_) (fun j hj => hx j (List.mem_cons_of_mem _ hj)) k
      unfold memWrite
      split
      · exact hx i (by simp)
      · exact hmv k'

/-- A resolved label is in the declared range. -/
theorem MemShape.index?_inRange {m : MemShape} {s : Bool} {idx : LVec} {k : Int} (h : m.index? s idx = some k) :
    m.inRange k := by
  unfold MemShape.index? at h
  cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] at h
  all_goals
    split at h
    · split at h
      · cases h; assumption
      · cases h
    · cases h

/-! ## The route's memory state, read as a memory view -/

/-- **The memory view of a route memory state**: each memory read through its identity (`memDecl?`, `lookupId`). -/
def CoreMemDesign.memOf (E : CoreMemDesign) (m : MemState) : MemV := fun n k =>
  match E.memDecl? n with
  | some md => ((m.lookupId md.shape.id).map fun blk => blk.read k).getD (LVec.xVec md.shape.elemWidth)
  | none => ⟨#[]⟩

/-- **A coherent memory state**: every memory's block is present under its identity (in the lookup and in the entry
table the route updates), with the declared shape, every read of the element width. -/
structure CoreMemDesign.MemCoherent (E : CoreMemDesign) (m : MemState) : Prop where
  blocks : ∀ md ∈ E.memories.toList, ∃ blk, m.lookupId md.shape.id = some blk ∧
    ((m.entries.find? fun p => p.1 == md.shape.id).map (·.2)) = some blk ∧ blk.shape = md.shape ∧
    ∀ k, (blk.read k).width = md.shape.elemWidth

theorem CoreMemDesign.memDecl?_some {E : CoreMemDesign} {n : String} {md : CoreMemDecl}
    (h : E.memDecl? n = some md) : md ∈ E.memories.toList ∧ md.source.name = n := by
  unfold CoreMemDesign.memDecl? at h
  exact ⟨List.mem_of_find?_eq_some h, by simpa using List.find?_some h⟩

theorem CoreMemDesign.memDecl?_none {E : CoreMemDesign} (hm : E.memories.toList = []) (n : String) :
    E.memDecl? n = none := by
  simp [CoreMemDesign.memDecl?, hm]

/-- A design without memories reads the empty memory view. -/
theorem CoreMemDesign.memOf_noMem {E : CoreMemDesign} (hm : E.memories.toList = []) (m : MemState) :
    E.memOf m = memNone := by
  funext n k
  simp [CoreMemDesign.memOf, CoreMemDesign.memDecl?_none hm, memNone]

/-- A design without memories: every memory state is coherent. -/
theorem CoreMemDesign.memCoherent_noMem {E : CoreMemDesign} (hm : E.memories.toList = []) (m : MemState) :
    E.MemCoherent m :=
  ⟨fun md hmd => by rw [hm] at hmd; simp at hmd⟩

/-- On a coherent memory state the route's run-time element read is `readV` on the memory view. -/
theorem CoreMemDesign.readIndexId_V {E : CoreMemDesign} {m : MemState} (hmc : E.MemCoherent m) {n : String}
    {md : CoreMemDecl} (hmd : E.memDecl? n = some md) (sg : Bool) (idx : LVec) :
    m.readIndexId md.shape.id sg idx = some (md.readV (E.memOf m) sg idx) := by
  obtain ⟨hmem, hname⟩ := CoreMemDesign.memDecl?_some hmd
  obtain ⟨blk, hb, -, hs, -⟩ := hmc.blocks md hmem
  have hmd' : E.memDecl? md.source.name = some md := by rw [hname]; exact hmd
  simp only [MemState.readIndexId, hb, Option.map_some, Option.some.injEq, MemBlock.readIndex, hs,
    CoreMemDecl.readV]
  cases md.shape.index? sg idx with
  | none => rfl
  | some k => simp [memRd, CoreMemDesign.memOf, hmd', hb]

/-! ## The route's expression evaluator on a view -/

/-- The evaluation width table `evalScalarLocals` uses. -/
def CoreMemDesign.widthsOf (E : CoreMemDesign) (elems : List (String × Nat)) : List (String × Nat) :=
  if elems.isEmpty then E.elems else elems

/-- `evalScalarLocals` without locals, on a view. -/
def CoreMemDesign.evalScalarV (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat)) (v : SvState)
    (ctx : Option Nat) (e : PExpr) : Res LVec :=
  evalPure2 v (instExpr2 env (E.widthsOf elems) ctx e)

mutual

/-- `evalIndexLocals` on a view. -/
def CoreMemDesign.evalIdxV (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat)) (v : SvState)
    (mv : MemV) (e : PExpr) : Res LVec :=
  match evalInt env e with
  | .ok i => .ok (LVec.ofInt 32 i)
  | .error _ => E.evalV env elems v mv none e

/-- `evalExprLocals` on a view and a memory view: the same arms in the same order; a one-rank element read of a memory
is its read equation (`readV`), other ranks and part selects of a memory the route's refusals. -/
def CoreMemDesign.evalV (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat)) (v : SvState)
    (mv : MemV) (ctx : Option Nat) : PExpr → Res LVec
  | e@(.arrayElem name [index]) =>
      match E.memDecl? name with
      | some md => do
          let idx ← E.evalIdxV env elems v mv index
          .ok (md.readV mv index.signedCast idx)
      | none => E.evalScalarV env elems v ctx e
  | e@(.arrayElem name _) =>
      if (E.memDecl? name).isSome then
        .unsupported s!"ArraySel:rank: memory '{name}' is not a one-rank element select"
      else E.evalScalarV env elems v ctx e
  | e@(.arrayPart name _ _ _ _) =>
      match E.memDecl? name with
      | some _ => .unsupported s!"ArraySel:part: memory '{name}' part select is outside this E slice"
      | none => E.evalScalarV env elems v ctx e
  | e@(.bitSel base index) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then do
        let bv ← E.evalV env elems v mv none base
        let iv ← E.evalIdxV env elems v mv index
        let position? := if index.signedCast then iv.toInt? else iv.toNat?.map Int.ofNat
        match position? with
        | some position =>
            if 0 ≤ position && position < bv.width then .ok (bv.extract position.toNat 1)
            else .ok (LVec.xVec 1)
        | none => .ok (LVec.xVec 1)
      else E.evalScalarV env elems v ctx e
  | .functionCall _ _ => .unsupported "evalV: a function call is outside the clocked profile"
  | e@(.unary op a) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then do
        evalMemUnary op (← E.evalV env elems v mv ctx a)
      else E.evalScalarV env elems v ctx e
  | e@(.binary op a b) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then do
        evalMemBin op (← E.evalV env elems v mv ctx a) (← E.evalV env elems v mv ctx b)
      else E.evalScalarV env elems v ctx e
  | e@(.ternary c a b) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then do
        let cv ← E.evalV env elems v mv none c
        let tv ← E.evalV env elems v mv ctx a
        let fv ← E.evalV env elems v mv ctx b
        .ok (LVec.ternary cv tv fv)
      else E.evalScalarV env elems v ctx e
  | e@(.concat xs) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then do
        let vs ← E.evalListV env elems v mv xs
        .ok (LVec.concatMany vs.toArray)
      else E.evalScalarV env elems v ctx e
  | e@(.resize _ a) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then do
        let x ← E.evalV env elems v mv ctx a
        .ok (x.resizeU (ctx.getD x.width))
      else E.evalScalarV env elems v ctx e
  | e@(.signedResize _ a) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then do
        let x ← E.evalV env elems v mv ctx a
        .ok (x.resizeSigned (ctx.getD x.width))
      else E.evalScalarV env elems v ctx e
  | e@(.squash2 _ a) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then do
        return (← E.evalV env elems v mv ctx a).toTwoState
      else E.evalScalarV env elems v ctx e
  | e => E.evalScalarV env elems v ctx e

/-- `evalMemExprListLocals` on a view. -/
def CoreMemDesign.evalListV (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat)) (v : SvState)
    (mv : MemV) : List PExpr → Res (List LVec)
  | [] => .ok []
  | e :: es => do
      let x ← E.evalV env elems v mv none e
      let xs ← E.evalListV env elems v mv es
      .ok (x :: xs)

end

mutual

theorem CoreMemDesign.evalIdx_eq {E : CoreMemDesign} {st : CoreMemState} (hmc : E.MemCoherent st.memory)
    (env : IEnv) (elems : List (String × Nat)) :
    ∀ (e : PExpr), LeanModels.Sv.PExpr.hasFunctionCall e = false →
      E.evalIndexLocals env elems st [] e = E.evalIdxV env elems (E.scalar.view st.scalar) (E.memOf st.memory) e
  | e, h => by
      unfold CoreMemDesign.evalIndexLocals CoreMemDesign.evalIdxV
      cases evalInt env e with
      | ok i => rfl
      | error m => exact CoreMemDesign.evalExprLocals_eq_evalV hmc env elems none e h

/-- **The route's evaluator is `evalV` on the view and the memory view**, on a coherent memory state, for a
function-free expression. -/
theorem CoreMemDesign.evalExprLocals_eq_evalV {E : CoreMemDesign} {st : CoreMemState} (hmc : E.MemCoherent st.memory)
    (env : IEnv) (elems : List (String × Nat)) :
    ∀ (ctx : Option Nat) (e : PExpr), LeanModels.Sv.PExpr.hasFunctionCall e = false →
      E.evalExprLocals env elems st ctx [] e =
        E.evalV env elems (E.scalar.view st.scalar) (E.memOf st.memory) ctx e
  | ctx, .lit _, _ => by
      simp [CoreMemDesign.evalExprLocals, CoreMemDesign.evalV, CoreMemDesign.evalScalarLocals,
        CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .ident _, _ => by
      simp [CoreMemDesign.evalExprLocals, CoreMemDesign.evalV, CoreMemDesign.evalScalarLocals,
        CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .paramRef _ _, _ => by
      simp [CoreMemDesign.evalExprLocals, CoreMemDesign.evalV, CoreMemDesign.evalScalarLocals,
        CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .genvarRef _, _ => by
      simp [CoreMemDesign.evalExprLocals, CoreMemDesign.evalV, CoreMemDesign.evalScalarLocals,
        CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .enumRef _ _ _, _ => by
      simp [CoreMemDesign.evalExprLocals, CoreMemDesign.evalV, CoreMemDesign.evalScalarLocals,
        CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .int _, _ => by
      simp [CoreMemDesign.evalExprLocals, CoreMemDesign.evalV, CoreMemDesign.evalScalarLocals,
        CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .fill _, _ => by
      simp [CoreMemDesign.evalExprLocals, CoreMemDesign.evalV, CoreMemDesign.evalScalarLocals,
        CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .unsupported _ _, _ => by
      simp [CoreMemDesign.evalExprLocals, CoreMemDesign.evalV, CoreMemDesign.evalScalarLocals,
        CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .typeBits _ _, _ => by
      simp [CoreMemDesign.evalExprLocals, CoreMemDesign.evalV, CoreMemDesign.evalScalarLocals,
        CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .sysCall _ _, h => by
      simp [LeanModels.Sv.PExpr.hasFunctionCall] at h
  | ctx, .partSel _ _ _, _ => by
      simp [CoreMemDesign.evalExprLocals, CoreMemDesign.evalV, CoreMemDesign.evalScalarLocals,
        CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .repl _ _, _ => by
      simp [CoreMemDesign.evalExprLocals, CoreMemDesign.evalV, CoreMemDesign.evalScalarLocals,
        CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .reduce _ _, _ => by
      simp [CoreMemDesign.evalExprLocals, CoreMemDesign.evalV, CoreMemDesign.evalScalarLocals,
        CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .cast _ _, _ => by
      simp [CoreMemDesign.evalExprLocals, CoreMemDesign.evalV, CoreMemDesign.evalScalarLocals,
        CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .functionCall _ _, h => by simp [LeanModels.Sv.PExpr.hasFunctionCall] at h
  | ctx, .arrayElem name indices, h => by
      cases indices with
      | nil =>
          unfold CoreMemDesign.evalExprLocals CoreMemDesign.evalV
          split <;> simp [CoreMemDesign.evalScalarLocals, CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
      | cons i is =>
          cases is with
          | nil =>
              simp only [LeanModels.Sv.PExpr.hasFunctionCall, LeanModels.Sv.PExpr.hasFunctionCallList,
                Bool.or_false] at h
              unfold CoreMemDesign.evalExprLocals CoreMemDesign.evalV
              cases hmd : E.memDecl? name with
              | none => simp [CoreMemDesign.evalScalarLocals, CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
              | some md =>
                  simp only [CoreMemDesign.evalIdx_eq hmc env elems i h]
                  cases E.evalIdxV env elems (E.scalar.view st.scalar) (E.memOf st.memory) i with
                  | ok iv => simp [CoreMemDesign.readIndexId_V hmc hmd]
                  | timeout => rfl
                  | unsupported m => rfl
          | cons j js =>
              unfold CoreMemDesign.evalExprLocals CoreMemDesign.evalV
              split <;> simp [CoreMemDesign.evalScalarLocals, CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .arrayPart name indices mode a b, _ => by
      unfold CoreMemDesign.evalExprLocals CoreMemDesign.evalV
      cases hmd : E.memDecl? name <;>
        simp [hmd, CoreMemDesign.evalScalarLocals, CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .aggregateMember base path, h => by
      simp [LeanModels.Sv.PExpr.hasFunctionCall] at h
  | ctx, .bitSel base index, h => by
      simp only [LeanModels.Sv.PExpr.hasFunctionCall, Bool.or_eq_false_iff] at h
      unfold CoreMemDesign.evalExprLocals CoreMemDesign.evalV
      split
      · rw [CoreMemDesign.evalExprLocals_eq_evalV hmc env elems none base h.1,
          CoreMemDesign.evalIdx_eq hmc env elems index h.2]
        rfl
      · simp [CoreMemDesign.evalScalarLocals, CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .unary op a, h => by
      simp only [LeanModels.Sv.PExpr.hasFunctionCall] at h
      unfold CoreMemDesign.evalExprLocals CoreMemDesign.evalV
      split
      · rw [CoreMemDesign.evalExprLocals_eq_evalV hmc env elems ctx a h]
      · simp [CoreMemDesign.evalScalarLocals, CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .binary op a b, h => by
      simp only [LeanModels.Sv.PExpr.hasFunctionCall, Bool.or_eq_false_iff] at h
      unfold CoreMemDesign.evalExprLocals CoreMemDesign.evalV
      split
      · rw [CoreMemDesign.evalExprLocals_eq_evalV hmc env elems ctx a h.1,
          CoreMemDesign.evalExprLocals_eq_evalV hmc env elems ctx b h.2]
      · simp [CoreMemDesign.evalScalarLocals, CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .ternary c a b, h => by
      simp only [LeanModels.Sv.PExpr.hasFunctionCall, Bool.or_eq_false_iff] at h
      unfold CoreMemDesign.evalExprLocals CoreMemDesign.evalV
      split
      · rw [CoreMemDesign.evalExprLocals_eq_evalV hmc env elems none c h.1.1,
          CoreMemDesign.evalExprLocals_eq_evalV hmc env elems ctx a h.1.2,
          CoreMemDesign.evalExprLocals_eq_evalV hmc env elems ctx b h.2]
      · simp [CoreMemDesign.evalScalarLocals, CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .concat xs, h => by
      simp only [LeanModels.Sv.PExpr.hasFunctionCall] at h
      unfold CoreMemDesign.evalExprLocals CoreMemDesign.evalV
      split
      · rw [CoreMemDesign.evalList_eq hmc env elems xs h]
      · simp [CoreMemDesign.evalScalarLocals, CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .resize w a, h => by
      simp only [LeanModels.Sv.PExpr.hasFunctionCall] at h
      unfold CoreMemDesign.evalExprLocals CoreMemDesign.evalV
      split
      · rw [CoreMemDesign.evalExprLocals_eq_evalV hmc env elems ctx a h]
      · simp [CoreMemDesign.evalScalarLocals, CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .signedResize w a, h => by
      simp only [LeanModels.Sv.PExpr.hasFunctionCall] at h
      unfold CoreMemDesign.evalExprLocals CoreMemDesign.evalV
      split
      · rw [CoreMemDesign.evalExprLocals_eq_evalV hmc env elems ctx a h]
      · simp [CoreMemDesign.evalScalarLocals, CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]
  | ctx, .squash2 w a, h => by
      simp only [LeanModels.Sv.PExpr.hasFunctionCall] at h
      unfold CoreMemDesign.evalExprLocals CoreMemDesign.evalV
      split
      · rw [CoreMemDesign.evalExprLocals_eq_evalV hmc env elems ctx a h]
      · simp [CoreMemDesign.evalScalarLocals, CoreMemDesign.evalScalarV, CoreMemDesign.widthsOf]

theorem CoreMemDesign.evalList_eq {E : CoreMemDesign} {st : CoreMemState} (hmc : E.MemCoherent st.memory)
    (env : IEnv) (elems : List (String × Nat)) :
    ∀ (xs : List PExpr), LeanModels.Sv.PExpr.hasFunctionCallList xs = false →
      E.evalMemExprListLocals env elems st [] xs =
        E.evalListV env elems (E.scalar.view st.scalar) (E.memOf st.memory) xs
  | [], _ => by simp [CoreMemDesign.evalMemExprListLocals, CoreMemDesign.evalListV]
  | x :: xs, h => by
      simp only [LeanModels.Sv.PExpr.hasFunctionCallList, Bool.or_eq_false_iff] at h
      simp only [CoreMemDesign.evalMemExprListLocals, CoreMemDesign.evalListV,
        CoreMemDesign.evalExprLocals_eq_evalV hmc env elems none x h.1, CoreMemDesign.evalList_eq hmc env elems xs h.2]

end

#print axioms CoreMemDesign.evalExprLocals_eq_evalV

theorem CoreMemDesign.evalExpr_eq {E : CoreMemDesign} {st : CoreMemState} (hmc : E.MemCoherent st.memory)
    (env : IEnv) (ctx : Option Nat) (e : PExpr) (h : LeanModels.Sv.PExpr.hasFunctionCall e = false) :
    E.evalExpr env E.elems st ctx e = E.evalV env E.elems (E.scalar.view st.scalar) (E.memOf st.memory) ctx e :=
  CoreMemDesign.evalExprLocals_eq_evalV hmc env E.elems ctx e h

theorem CoreMemDesign.evalIndex_eq {E : CoreMemDesign} {st : CoreMemState} (hmc : E.MemCoherent st.memory)
    (env : IEnv) (e : PExpr) (h : LeanModels.Sv.PExpr.hasFunctionCall e = false) :
    E.evalIndex env E.elems st e = E.evalIdxV env E.elems (E.scalar.view st.scalar) (E.memOf st.memory) e :=
  CoreMemDesign.evalIdx_eq hmc env E.elems e h

/-! ## Edge bodies: the route's executor on views

`execV` is `execStmtFuel` with the state replaced by its view and memory view: the same arms in the same order, the
same refusal messages. A blocking write changes the view (`setV`: `setScalarState`'s conversion to the declaration's
type; a select or concatenation target through the route's own window resolver), a nonblocking write issues queue
entries (the whole signal, `scalarNbaWindows` of the resolved windows, or a memory element's record, `issueV`), `case`
selects by the §12.5 matcher (`caseHit` per mode) with the route's qualified-case claim check. A procedural `for` loop
of nonblocking writes is the route's own: the header's value list (`forValues2`, a function of the parameters) and
the body folded over it under the iterator's binding (`execLoopV`, the route's `execLoopValuesFuel`); the list is never
unrolled. The environment is an argument because a loop body runs under `env.bindVal iterator i`. A blocking write to
a memory element, and a loop whose body has a blocking assignment or a further loop, are refused by name. -/

mutual

/-- Whether a write target's index expressions call a function. -/
def _root_.LeanModels.Sv.PLhs.hasCall : PLhs → Bool
  | .ident _ => false
  | .bitSel _ i => LeanModels.Sv.PExpr.hasFunctionCall i
  | .partSel _ a b => LeanModels.Sv.PExpr.hasFunctionCall a || LeanModels.Sv.PExpr.hasFunctionCall b
  | .arrayElem _ is => LeanModels.Sv.PExpr.hasFunctionCallList is
  | .arrayPart _ is _ a b => LeanModels.Sv.PExpr.hasFunctionCallList is || LeanModels.Sv.PExpr.hasFunctionCall a ||
      LeanModels.Sv.PExpr.hasFunctionCall b
  | .aggregateMember .. => true
  | .arrayBitSel .. => true
  | .concat parts => PLhs.hasCallList parts

/-- `hasCall` of a list of targets. -/
def _root_.LeanModels.Sv.PLhs.hasCallList : List PLhs → Bool
  | [] => false
  | p :: ps => PLhs.hasCall p || PLhs.hasCallList ps

end

mutual

/-- **The body of a procedural `for` loop the clocked views mirror**: nonblocking writes (whole signals, selects,
concatenations, memory elements) under `if`, `case` and blocks. No blocking assignment (an iteration would read what an
earlier one wrote), no declaration, no nested loop. Such a body leaves the view as it was (`execV_loopBody`), so every
iteration reads the same view and the loop is its issued updates, in order. -/
def _root_.LeanModels.Sv.PStmt.loopBodyB : PStmt → Bool
  | .nbaAssign .. => true
  | .nbaAssignL .. => true
  | .ifStmt _ y n => PStmt.loopBodyB y && PStmt.optLoopBodyB n
  | .block body => PStmt.listLoopBodyB body
  | .caseStmt _ items d _ _ => PStmt.itemsLoopBodyB items && PStmt.optLoopBodyB d
  | _ => false
termination_by structural s => s

/-- `loopBodyB` of an optional statement. -/
def _root_.LeanModels.Sv.PStmt.optLoopBodyB : Option PStmt → Bool
  | none => true
  | some s => PStmt.loopBodyB s
termination_by structural o => o

/-- `loopBodyB` of every statement of a list. -/
def _root_.LeanModels.Sv.PStmt.listLoopBodyB : List PStmt → Bool
  | [] => true
  | s :: ss => PStmt.loopBodyB s && PStmt.listLoopBodyB ss
termination_by structural xs => xs

/-- `loopBodyB` of the arms of a `case`. -/
def _root_.LeanModels.Sv.PStmt.itemsLoopBodyB : List (List PExpr × PStmt) → Bool
  | [] => true
  | (_, b) :: rest => PStmt.loopBodyB b && PStmt.itemsLoopBodyB rest
termination_by structural xs => xs

end

mutual

/-- An edge body the view-level executor mirrors: blocking and nonblocking writes (whole signals, selects,
concatenations, memory elements), `if`, `case` (every mode, plain and qualified), blocks, every expression (targets'
indices included) function-free, and a procedural `for` loop whose body is a loop body of the profile (`loopBodyB`:
nonblocking writes only, no nested loop; the header is the route's `forValues2`, evaluated on the parameters alone). A
loop with a blocking assignment or a further loop in its body and a statement ingestion kept unconverted are outside. -/
def _root_.LeanModels.Sv.PStmt.edgeOkB : PStmt → Bool
  | .nbaAssign _ e => !LeanModels.Sv.PExpr.hasFunctionCall e
  | .blockingAssign _ e => !LeanModels.Sv.PExpr.hasFunctionCall e
  | .nbaAssignL t e => !LeanModels.Sv.PExpr.hasFunctionCall e && !PLhs.hasCall t
  | .blockingAssignL t e => !LeanModels.Sv.PExpr.hasFunctionCall e && !PLhs.hasCall t
  | .ifStmt c y n => !LeanModels.Sv.PExpr.hasFunctionCall c && PStmt.edgeOkB y && PStmt.optEdgeOkB n
  | .block body => PStmt.listEdgeOkB body
  | .caseStmt s items d _ _ =>
      !LeanModels.Sv.PExpr.hasFunctionCall s && PStmt.itemsEdgeOkB items && PStmt.optEdgeOkB d
  | .localDecl .. => false
  | .automaticDecl .. => false
  | .forLoop _ _ _ _ body => PStmt.edgeOkB body && PStmt.loopBodyB body
  | .unsupported .. => false
termination_by structural s => s

/-- `edgeOkB` of an optional statement. -/
def _root_.LeanModels.Sv.PStmt.optEdgeOkB : Option PStmt → Bool
  | none => true
  | some s => PStmt.edgeOkB s
termination_by structural o => o

/-- `edgeOkB` of every statement of a list. -/
def _root_.LeanModels.Sv.PStmt.listEdgeOkB : List PStmt → Bool
  | [] => true
  | s :: ss => PStmt.edgeOkB s && PStmt.listEdgeOkB ss
termination_by structural xs => xs

/-- `edgeOkB` of the arms of a `case`, their patterns function-free. -/
def _root_.LeanModels.Sv.PStmt.itemsEdgeOkB : List (List PExpr × PStmt) → Bool
  | [] => true
  | (ps, b) :: rest =>
      !LeanModels.Sv.PExpr.hasFunctionCallList ps && PStmt.edgeOkB b && PStmt.itemsEdgeOkB rest
termination_by structural xs => xs

end

mutual

/-- The fuel need of a loop body of the profile does not read the environment. -/
theorem _root_.LeanModels.Sv.PStmt.need_env (env env' : IEnv) :
    ∀ (s : PStmt), PStmt.loopBodyB s = true → PStmt.need env s = PStmt.need env' s
  | .ifStmt _ y n, h => by
      simp only [PStmt.loopBodyB, Bool.and_eq_true] at h
      simp only [PStmt.need, PStmt.need_env env env' y h.1, PStmt.optNeed_env env env' n h.2]
  | .block body, h => by
      simp only [PStmt.loopBodyB] at h
      simp only [PStmt.need, PStmt.listNeed_env env env' body h]
  | .caseStmt _ items d _ _, h => by
      simp only [PStmt.loopBodyB, Bool.and_eq_true] at h
      simp only [PStmt.need, PStmt.itemsNeed_env env env' items h.1, PStmt.optNeed_env env env' d h.2]
  | .nbaAssign .., _ => by simp only [PStmt.need]
  | .nbaAssignL .., _ => by simp only [PStmt.need]
  | .forLoop .., h => by simp [PStmt.loopBodyB] at h
  | .localDecl .., h => by simp [PStmt.loopBodyB] at h
  | .automaticDecl .., h => by simp [PStmt.loopBodyB] at h
  | .blockingAssign .., h => by simp [PStmt.loopBodyB] at h
  | .blockingAssignL .., h => by simp [PStmt.loopBodyB] at h
  | .unsupported .., h => by simp [PStmt.loopBodyB] at h

theorem _root_.LeanModels.Sv.PStmt.optNeed_env (env env' : IEnv) :
    ∀ (o : Option PStmt), PStmt.optLoopBodyB o = true → PStmt.optNeed env o = PStmt.optNeed env' o
  | none, _ => by simp only [PStmt.optNeed]
  | some s, h => by
      simp only [PStmt.optLoopBodyB] at h
      simp only [PStmt.optNeed, PStmt.need_env env env' s h]

theorem _root_.LeanModels.Sv.PStmt.listNeed_env (env env' : IEnv) :
    ∀ (ss : List PStmt), PStmt.listLoopBodyB ss = true → PStmt.listNeed env ss = PStmt.listNeed env' ss
  | [], _ => by simp only [PStmt.listNeed]
  | s :: ss, h => by
      simp only [PStmt.listLoopBodyB, Bool.and_eq_true] at h
      simp only [PStmt.listNeed, PStmt.need_env env env' s h.1, PStmt.listNeed_env env env' ss h.2]

theorem _root_.LeanModels.Sv.PStmt.itemsNeed_env (env env' : IEnv) :
    ∀ (items : List (List PExpr × PStmt)), PStmt.itemsLoopBodyB items = true →
      PStmt.itemsNeed env items = PStmt.itemsNeed env' items
  | [], _ => by simp only [PStmt.itemsNeed]
  | (_, b) :: rest, h => by
      simp only [PStmt.itemsLoopBodyB, Bool.and_eq_true] at h
      simp only [PStmt.itemsNeed, PStmt.need_env env env' b h.1, PStmt.itemsNeed_env env env' rest h.2]

end

/-- The value `storeFromView` gives a declaration the view lacks. -/
def declFallback (dc : Decl) : LVec := if dc.isNet then LVec.replicate dc.width .lz else LVec.xVec dc.width

/-- The view `storeFromView` materializes: each declaration's value from `raw`, converted to its type. -/
def CoreMemDesign.matV (E : CoreMemDesign) (raw : SvState) : SvState :=
  E.scalar.decls.toList.map fun dc =>
    (dc.name, (Val.ofLVec (VType.ofDecl dc) ((SvState.lookup raw dc.name).getD (declFallback dc))).bits)

/-- `setScalarState` on a view: the value converted to its declaration's type (a name the scalar view does not resolve
is left alone, as the route leaves the state). -/
def CoreMemDesign.setV (E : CoreMemDesign) (v : SvState) (n : String) (x : LVec) : SvState :=
  match E.scalar.resolve n with
  | some id =>
      match E.scalar.declOf id with
      | some dc => SvState.set v n (Val.ofLVec (VType.ofDecl dc) x).bits
      | none => v
  | none => v

/-- `writeScalarLhs2` on a view: a concatenation written window by window (`writeConcatLhs2`) and materialized as
`compactScalar` does; a select written into its window of the old value; a no-write window (an x/z or out-of-range
index, §11.5.1) changes nothing. -/
def CoreMemDesign.writeLhsV (E : CoreMemDesign) (v : SvState) (lhs : Lhs2) (value : LVec) : Res SvState :=
  match lhs with
  | .concat _ => do
      let windows ← resolveConcatLhs2 4096 v lhs
      let v' ← writeConcatLhs2 v value windows
      .ok (E.matV v')
  | _ => do
      let (name, window) ← resolveLhs2 4096 v lhs
      match window with
      | none => .ok v
      | some (lo, width) =>
          match E.scalar.resolve name with
          | none => .unsupported s!"11.5.1: scalar select target '{name}' is undeclared"
          | some _ => .ok (E.setV v name (((SvState.lookup v name).getD ⟨#[]⟩).insertAt lo (value.resizeU width)))

/-- `coreMemCaseHits` on a view: how many arms have a pattern that hits the subject. -/
def CoreMemDesign.caseHitsV (E : CoreMemDesign) (env : IEnv) (v : SvState) (mv : MemV) (subject : LVec) (mode : CaseMode) :
    List (List PExpr × PStmt) → Res Nat
  | [] => .ok 0
  | (patterns, _) :: rest => do
      let values ← E.evalListV env E.elems v mv patterns
      let n ← E.caseHitsV env v mv subject mode rest
      .ok (if values.any (fun value => caseHit mode subject value) then n + 1 else n)

/-- The result of an edge body on views: the view after its blocking writes, the scalar nonblocking updates and the
memory records it issues, each in issue order. -/
abbrev ExecV := SvState × NbaQueue2 × MemQV

/-- **The route's loop fold on views** (`execLoopValuesFuel`), for a loop body of the profile (`loopBodyB`: it leaves
the view as it was): the body's run `step i` at each value of the header's value list, in order, each on the same view
`v`; the issued updates and memory records concatenated in issue order. The list is the header's (`forValues2`: a
function of the parameters), never unrolled; `step i` is the body under the iterator's binding `env.bindVal it i`. -/
def execLoopV (v : SvState) (step : Int → Res ExecV) : List Int → Res ExecV
  | [] => .ok (v, [], [])
  | i :: rest => do
      let a ← step i
      let b ← execLoopV v step rest
      .ok (v, a.2.1 ++ b.2.1, a.2.2 ++ b.2.2)

/-- The loop fold leaves the view as it was. -/
theorem execLoopV_fst {v : SvState} {step : Int → Res ExecV} :
    ∀ {values : List Int} {r : ExecV}, execLoopV v step values = .ok r → r.1 = v
  | [], r, h => by
      simp only [execLoopV, Res.ok.injEq] at h
      subst h
      rfl
  | i :: rest, r, h => by
      simp only [execLoopV, Res.bind_eq_ok, Res.ok.injEq] at h
      obtain ⟨a, -, b, -, rfl⟩ := h
      rfl

/-- **The loop fold in closed form**: when every iteration issues `q i` and `m i`, the loop issues their
concatenation over the value list (`List.flatMap`: the list stays the header's, a function of the parameters). -/
theorem execLoopV_ok (v : SvState) (w : Int → SvState) (q : Int → NbaQueue2) (m : Int → MemQV) :
    ∀ (values : List Int), execLoopV v (fun i => .ok (w i, q i, m i)) values =
      .ok (v, values.flatMap q, values.flatMap m)
  | [] => rfl
  | i :: rest => by
      simp only [execLoopV, execLoopV_ok v w q m rest, Res.ok_bind, List.flatMap_cons]

/-- A procedural loop whose body consists only of memory NBAs leaves the scalar
view and scalar NBA queue unchanged.  The memory records remain in issue order
as the flat map of the loop values. -/
theorem execLoopV_memory (v : SvState) (m : Int → MemQV) :
    ∀ (values : List Int),
      execLoopV v (fun i => .ok (v, [], m i)) values =
        .ok (v, [], values.flatMap m)
  | [] => rfl
  | i :: rest => by
      simp only [execLoopV, execLoopV_memory v m rest, Res.ok_bind, List.nil_append, List.flatMap_cons]

mutual

/-- **The route's edge-body executor on views** (`execStmtFuel`): the view after the body's blocking writes, and the
nonblocking updates and memory records it issues, in issue order. The memory view is read, never written: a blocking
write to a memory element is refused by name. A procedural `for` loop whose body is a loop body of the profile
(`loopBodyB`) is the fold of its body over the header's value list (`execLoopV` over `forValues2`), the body under
`env.bindVal iterator i`; any other loop is refused by name. -/
def CoreMemDesign.execV (E : CoreMemDesign) (env : IEnv) (v : SvState) (mv : MemV) : PStmt → Res ExecV
  | .nbaAssign t e =>
      match E.scalarTarget t with
      | none => .unsupported s!"11.5.1: scalar NBA target '{t}' is undeclared"
      | some w => do
          let x ← E.evalV env E.elems v mv (some w) e
          .ok (v, [(t, 0, x)], [])
  | .nbaAssignL lhs e =>
      match lhs with
      | .ident t =>
          match E.scalarTarget t with
          | none => .unsupported s!"11.5.1: scalar NBA target '{t}' is undeclared"
          | some w => do
              let x ← E.evalV env E.elems v mv (some w) e
              .ok (v, [(t, 0, x)], [])
      | .arrayElem name indices =>
          match E.memDecl? name with
          | none => do
              let lw ← E.scalarLhs2 env E.elems (.arrayElem name indices)
              let x ← E.evalV env E.elems v mv (some lw.2) e
              let windows ← resolveConcatLhs2 4096 v lw.1
              .ok (v, scalarNbaWindows x windows, [])
          | some md =>
              match indices with
              | [index] => do
                  let x ← E.evalV env E.elems v mv (some md.shape.elemWidth) e
                  let iv ← E.evalIdxV env E.elems v mv index
                  .ok (v, [], md.issueV index.signedCast iv x)
              | _ => .unsupported s!"11.5.1: memory target '{name}' is not one-rank"
      | target => do
          let lw ← E.scalarLhs2 env E.elems target
          let x ← E.evalV env E.elems v mv (some lw.2) e
          let windows ← resolveConcatLhs2 4096 v lw.1
          .ok (v, scalarNbaWindows x windows, [])
  | .blockingAssign n e =>
      match E.scalarTarget n with
      | none => .unsupported s!"9.2.2.1: scalar edge target '{n}' is undeclared"
      | some w => do
          let x ← E.evalV env E.elems v mv (some w) e
          .ok (E.setV v n x, [], [])
  | .blockingAssignL lhs e =>
      match lhs with
      | .ident n =>
          match E.scalarTarget n with
          | none => .unsupported s!"9.2.2.1: scalar edge target '{n}' is undeclared"
          | some w => do
              let x ← E.evalV env E.elems v mv (some w) e
              .ok (E.setV v n x, [], [])
      | .arrayElem name indices =>
          match E.memDecl? name with
          | none => do
              let lw ← E.scalarLhs2 env E.elems (.arrayElem name indices)
              let x ← E.evalV env E.elems v mv (some lw.2) e
              let v' ← E.writeLhsV v lw.1 x
              .ok (v', [], [])
          | some _ =>
              .unsupported s!"9.2.2.1: a blocking write to the memory '{name}' in an edge body is outside the clocked profile (the memories slice, next)"
      | target => do
          let lw ← E.scalarLhs2 env E.elems target
          let x ← E.evalV env E.elems v mv (some lw.2) e
          let v' ← E.writeLhsV v lw.1 x
          .ok (v', [], [])
  | .ifStmt c y n => do
      let cv ← E.evalV env E.elems v mv (some 1) c
      if cv.condTrue then E.execV env v mv y else E.execOptV env v mv n
  | .block body => E.execListV env v mv body
  | .caseStmt subject items d mode check => do
      let sv ← E.evalV env E.elems v mv none subject
      match check with
      | .none => E.execItemsV env v mv sv mode items (E.execOptV env v mv d)
      | qualifier => do
          let n ← E.caseHitsV env v mv sv mode items
          if caseClaimOk qualifier d.isSome n then E.execItemsV env v mv sv mode items (E.execOptV env v mv d)
          else .unsupported s!"12.5.3: {caseCheckName qualifier}"
  | .localDecl .. =>
      .unsupported "9.4.2: a procedural local declaration in an edge body is outside the clocked profile"
  | .automaticDecl .. =>
      .unsupported "9.4.2: an automatic procedural declaration in an edge body is outside the clocked profile"
  | .forLoop iterator init condition step body =>
      if PStmt.loopBodyB body then
        match forValues2 env iterator init condition step with
        | .timeout => .timeout
        | .unsupported e => .unsupported s!"ForLoopStatement: {e}"
        | .ok values => execLoopV v (fun i => E.execV (env.bindVal iterator i) v mv body) values
      else
        .unsupported "9.4.2: a procedural `for` loop whose body has a blocking assignment, a declaration or a nested loop is outside the clocked profile"
  | .unsupported kind text => .unsupported s!"{kind}: {text}"
termination_by structural s => s

/-- `execV` of an optional statement (none changes nothing). -/
def CoreMemDesign.execOptV (E : CoreMemDesign) (env : IEnv) (v : SvState) (mv : MemV) : Option PStmt → Res ExecV
  | none => .ok (v, [], [])
  | some s => E.execV env v mv s
termination_by structural o => o

/-- `execV` of a statement list: the view threaded, the queues concatenated in order. -/
def CoreMemDesign.execListV (E : CoreMemDesign) (env : IEnv) (v : SvState) (mv : MemV) : List PStmt → Res ExecV
  | [] => .ok (v, [], [])
  | s :: ss => do
      let a ← E.execV env v mv s
      let b ← E.execListV env a.1 mv ss
      .ok (b.1, a.2.1 ++ b.2.1, a.2.2 ++ b.2.2)
termination_by structural xs => xs

/-- The arms of a `case`: the first item one of whose patterns hits the subject (§12.5, `caseHit` per mode) runs;
when no item hits, `dflt` (the caller passes the default's run: a value, so a pure function may take it whether or not
it is selected). -/
def CoreMemDesign.execItemsV (E : CoreMemDesign) (env : IEnv) (v : SvState) (mv : MemV) (sv : LVec) (mode : CaseMode) :
    List (List PExpr × PStmt) → Res ExecV → Res ExecV
  | [], dflt => dflt
  | (patterns, body) :: rest, dflt => do
      let values ← E.evalListV env E.elems v mv patterns
      if values.any (fun value => caseHit mode sv value) then E.execV env v mv body
      else E.execItemsV env v mv sv mode rest dflt
termination_by structural xs => xs


end
/-- The view executor's procedural-loop arm for a body whose per-iteration
memory receipt is already established.  The header remains the parser-native
`forValues2` list and is never unrolled by this theorem. -/
theorem CoreMemDesign.execV_forLoop_memory {E : CoreMemDesign} (env : IEnv) (v : SvState) (mv : MemV)
    {it : String} {init condition step : PExpr} {body : PStmt} {values : List Int} (m : Int → MemQV)
    (hbody : ∀ i, E.execV (env.bindVal it i) v mv body = .ok (v, [], m i))
    (hloop : PStmt.loopBodyB body = true)
    (hvals : forValues2 env it init condition step = .ok values) :
    E.execV env v mv (.forLoop it init condition step body) =
      .ok (v, [], values.flatMap m) := by
  simp only [CoreMemDesign.execV, hloop, ↓reduceIte, hvals]
  have hfun : (fun i => E.execV (env.bindVal it i) v mv body) =
      (fun i => .ok (v, [], m i)) := by
    funext i
    exact hbody i
  rw [hfun, execLoopV_memory]


/-! ## A plain `always` on one clock edge is an edge process

Ingestion keeps a plain `always @(posedge clk)` / `always @(posedge clk or negedge rst_n)` as an EVENT process
(`CoreMemProc.event`: the event list as written, §9.4.2). IEEE 1800-2017 §9.2.2.1 and §9.2.2.4: `always_ff` adds
restrictions to `always`, not behaviour, so on an event list of exactly one clock edge with an optional second edge
(the asynchronous reset) the two execute alike. Here that is a fact about the route, not an assumption: the route's
firing test of such a list is the edge process's (`coreMemEventEdge?_spec`: the same §9.4.2 edge table on bit 0, x and z
rows included) and its edge pass runs the two alike (`CoreMemDesign.runEdges_event`: the same body on the same state).
Neither runs at time zero (the edge pass belongs to a slot). The FIRST edge of the list is read as the clock and the
second as the reset: the roles do not matter to the route (its test is the disjunction), only to the input discipline
and the obligations stated per role. A list with a level-change member (`@(a)`), or with more than two members, is no
edge process (`none`) and stays outside the clocked profile. -/

/-- The edge an event-list member names (`posedge`, `negedge`); a level-change member (`@(a)`) names none. -/
def CoreMemEvent.clockEdge? (e : CoreMemEvent) : Option ClockEdge :=
  match e.edge with
  | .posedge => some .posedge
  | .negedge => some .negedge
  | .any => none

/-- **The edge process a plain `always` event list stands for**: exactly one clock edge, with an optional second edge
(the asynchronous reset: active-high for `posedge`, active-low for `negedge`). -/
def coreMemEventEdge? : List CoreMemEvent → PStmt → Option CoreMemEdge
  | [c], body =>
      match c.clockEdge? with
      | some k => some { clock := c.signal, edge := k, body := body, style := .alwaysPlain }
      | none => none
  | [c, r], body =>
      match c.clockEdge?, r.clockEdge? with
      | some k, some .posedge =>
          some { clock := c.signal, edge := k, reset := some r.signal, resetHigh := true, body := body,
                 style := .alwaysPlain }
      | some k, some .negedge =>
          some { clock := c.signal, edge := k, reset := some r.signal, resetHigh := false, body := body,
                 style := .alwaysPlain }
      | _, _ => none
  | _, _ => none

/-- **The edge process a process is**: an edge process itself, or a plain `always` on one clock edge with an optional
asynchronous reset edge (`coreMemEventEdge?`). -/
def CoreMemProc.edge? : CoreMemProc → Option CoreMemEdge
  | .edge f => some f
  | .event evs body => coreMemEventEdge? evs body
  | _ => none

/-- **The route's firing test and body of such an event list are the edge process's** (§9.4.2: the same edge table on
bit 0 of the same signals). -/
theorem coreMemEventEdge?_spec {evs : List CoreMemEvent} {body : PStmt} {f : CoreMemEdge}
    (h : coreMemEventEdge? evs body = some f) (a b : SvState) :
    coreMemEventsFire a b evs = f.fires a b ∧ f.body = body := by
  rcases evs with _ | ⟨c, _ | ⟨r, _ | ⟨x, xs⟩⟩⟩
  · simp [coreMemEventEdge?] at h
  · rcases c with ⟨cs, ce⟩
    cases ce <;> simp [coreMemEventEdge?, CoreMemEvent.clockEdge?] at h <;> subst h <;>
      simp [coreMemEventsFire, coreMemEventFires, CoreMemEdge.fires]
  · rcases c with ⟨cs, ce⟩
    rcases r with ⟨rs, re⟩
    cases ce <;> cases re <;> simp [coreMemEventEdge?, CoreMemEvent.clockEdge?] at h <;> subst h <;>
      simp [coreMemEventsFire, coreMemEventFires, CoreMemEdge.fires]
  · simp [coreMemEventEdge?] at h

/-- **A plain `always` on one clock edge steps exactly like the edge process** in the route's edge pass. -/
theorem CoreMemDesign.runEdges_event {E : CoreMemDesign} {env : IEnv} {elems : List (String × Nat)}
    {st : CoreMemState} {before after : SvState} {evs : List CoreMemEvent} {body : PStmt} {f : CoreMemEdge}
    (h : coreMemEventEdge? evs body = some f) (rest : List CoreMemProc) :
    E.runEdges env elems st before after (.event evs body :: rest) =
      E.runEdges env elems st before after (.edge f :: rest) := by
  obtain ⟨hf, hb⟩ := coreMemEventEdge?_spec h before after
  simp only [CoreMemDesign.runEdges, hf, hb]

/-! ## Events: what a design's edge processes are sensitive to, computed from the design

A design declares no clock. An EVENT is an edge (§9.4.2: the edge of a signal's least significant bit, x and z
included) some edge process is sensitive to: each edge process's clock edge (rising or falling), and the assertion edge
of its asynchronous reset (the fall of an active-low reset, the rise of an active-high one). The route's own firing test
`CoreMemEdge.fires` is "some event of the process occurs" (`CoreMemEdge.fires_eq`), so events are not a parallel notion.
Level events (`always_latch`, `always @*`) are outside the clocked profile: the scheduler's. -/

/-- An event of a design: an edge of a signal some edge process is sensitive to. -/
structure SeqEvent where
  src : String
  kind : ClockEdge
deriving DecidableEq, Repr

/-- The §9.4.2 edge table for one edge kind. -/
def edgeOf : ClockEdge → Logic → Logic → Bool
  | .posedge, x, y => isPosedge x y
  | .negedge, x, y => isNegedge x y

/-- The event occurs from the view `a` to the view `b` (bit 0 of its signal, §9.4.2). -/
def SeqEvent.occursIn (e : SeqEvent) (a b : SvState) : Bool := edgeOf e.kind (a.bit0 e.src) (b.bit0 e.src)

/-- An edge process's clock event. -/
def CoreMemEdge.clockEvent (f : CoreMemEdge) : SeqEvent := ⟨f.clock, f.edge⟩

/-- An edge process's reset event: the assertion edge of its asynchronous reset. -/
def CoreMemEdge.resetEvent? (f : CoreMemEdge) : Option SeqEvent :=
  f.reset.map fun r => ⟨r, if f.resetHigh then .posedge else .negedge⟩

/-- The events an edge process is sensitive to. -/
def CoreMemEdge.events (f : CoreMemEdge) : List SeqEvent := f.clockEvent :: f.resetEvent?.toList

/-- The events of a process (none for a process that is not an edge process). -/
def CoreMemProc.events : CoreMemProc → List SeqEvent
  | .edge f => f.events
  | .event evs body =>
      match coreMemEventEdge? evs body with
      | some f => f.events
      | none => []
  | _ => []

/-- A process's events are its edge process's. -/
theorem CoreMemProc.events_eq (p : CoreMemProc) :
    p.events = match p.edge? with
      | some f => f.events
      | none => [] := by
  cases p <;> rfl

/-- **The edge processes of a design**, in process order (a plain `always` on one clock edge read as one). -/
def CoreMemDesign.edgeProcs (E : CoreMemDesign) : List CoreMemEdge := E.processes.toList.filterMap CoreMemProc.edge?

/-- The old follow-up test that scanned only the normalized edge-process view. -/
def CoreMemDesign.firesEdges (E : CoreMemDesign) (a b : SvState) : Bool :=
  E.edgeProcs.any (fun f => f.fires a b)

/-- Every retained event process is one of the clock-edge forms admitted by `edge?`.
This is the condition under which the process-wide follow-up test is exactly the
old edge-process test. -/
def CoreMemDesign.allEventsAreEdges (E : CoreMemDesign) : Prop :=
  ∀ evs body, CoreMemProc.event evs body ∈ E.processes.toList →
    ∃ f, coreMemEventEdge? evs body = some f

/-- **R13 conservativity**: when a design has no non-edge plain `always` event,
the broadened in-slot follow-up test is equal to the former edge-only test. -/
theorem CoreMemDesign.firesAny_eq_firesEdges_of_allEventsAreEdges
    {E : CoreMemDesign} {a b : SvState} (hall : E.allEventsAreEdges) :
    E.firesAny a b = E.firesEdges a b := by
  unfold CoreMemDesign.firesAny CoreMemDesign.firesEdges CoreMemDesign.edgeProcs
  have aux : ∀ (ps : List CoreMemProc),
      (∀ p ∈ ps, p.edge? = none → CoreMemProc.firesIn a b p = false) →
      ps.any (CoreMemProc.firesIn a b) =
        (List.filterMap CoreMemProc.edge? ps).any (fun f => f.fires a b) := by
    intro ps
    induction ps with
    | nil => intro _; simp
    | cons p ps ih =>
      intro hp
      have htail : ∀ q ∈ ps, q.edge? = none → CoreMemProc.firesIn a b q = false := by
        intro q hq hn
        exact hp q (by simp [hq]) hn
      have iht := ih htail
      cases p with
      | edge f => simp [CoreMemProc.edge?, CoreMemProc.firesIn, iht]
      | event evs body =>
          cases he : coreMemEventEdge? evs body with
          | none =>
              have hzero := hp (.event evs body) (by simp)
                (by simp [CoreMemProc.edge?, he])
              have hfalse : coreMemEventsFire a b evs = false := by
                simpa [CoreMemProc.firesIn] using hzero
              simp [CoreMemProc.edge?, CoreMemProc.firesIn, he, hfalse, iht]
          | some f =>
              have hfire := coreMemEventEdge?_spec he a b |>.1
              simp [CoreMemProc.edge?, CoreMemProc.firesIn, he, hfire, iht]
      | assign target value => simp [CoreMemProc.edge?, CoreMemProc.firesIn, iht]
      | primitive op target inputs => simp [CoreMemProc.edge?, CoreMemProc.firesIn, iht]
      | initial body => simp [CoreMemProc.edge?, CoreMemProc.firesIn, iht]
      | _ => simp [CoreMemProc.edge?, CoreMemProc.firesIn, iht]
  apply aux E.processes.toList
  intro p hp hn
  cases p with
  | event evs body =>
      obtain ⟨f, hf⟩ := hall evs body hp
      simp [CoreMemProc.edge?, hf] at hn
  | edge f => simp [CoreMemProc.edge?] at hn
  | _ => simp [CoreMemProc.firesIn]

#print axioms CoreMemDesign.firesAny_eq_firesEdges_of_allEventsAreEdges

theorem CoreMemDesign.mem_edgeProcs {E : CoreMemDesign} {f : CoreMemEdge} :
    f ∈ E.edgeProcs ↔ ∃ p ∈ E.processes.toList, p.edge? = some f := by
  simp [CoreMemDesign.edgeProcs, List.mem_filterMap]

/-- An edge process of the design is one of its edge processes. -/
theorem CoreMemDesign.edge_mem_edgeProcs {E : CoreMemDesign} {f : CoreMemEdge}
    (h : CoreMemProc.edge f ∈ E.processes.toList) : f ∈ E.edgeProcs :=
  CoreMemDesign.mem_edgeProcs.mpr ⟨_, h, rfl⟩

/-- **The events of a design**, computed from its edge processes. -/
def CoreMemDesign.events (E : CoreMemDesign) : List SeqEvent := E.processes.toList.flatMap CoreMemProc.events

/-- The event sources of a design: the signals its events are edges of. -/
def CoreMemDesign.sources (E : CoreMemDesign) : List String := E.events.map SeqEvent.src

/-- The events of the design that occur from the view `a` to the view `b`. -/
def CoreMemDesign.occurs (E : CoreMemDesign) (a b : SvState) : List SeqEvent := E.events.filter (·.occursIn a b)

/-- **The route's firing test is "some event of the process occurs"**. -/
theorem CoreMemEdge.fires_eq (f : CoreMemEdge) (a b : SvState) : f.fires a b = f.events.any (·.occursIn a b) := by
  unfold CoreMemEdge.fires CoreMemEdge.events CoreMemEdge.clockEvent CoreMemEdge.resetEvent?
  cases f.reset with
  | none => cases f.edge <;> simp [SeqEvent.occursIn, edgeOf]
  | some r => cases f.edge <;> cases f.resetHigh <;> simp [SeqEvent.occursIn, edgeOf]

/-- An event of a design is an event of one of its processes. -/
theorem CoreMemDesign.mem_events {E : CoreMemDesign} {e : SeqEvent} :
    e ∈ E.events ↔ ∃ f, f ∈ E.edgeProcs ∧ e ∈ f.events := by
  simp only [CoreMemDesign.events, List.mem_flatMap, CoreMemDesign.mem_edgeProcs]
  constructor
  · rintro ⟨p, hp, he⟩
    rw [CoreMemProc.events_eq] at he
    cases hpe : p.edge? with
    | none => simp [hpe] at he
    | some f => exact ⟨f, ⟨p, hp, hpe⟩, by simpa [hpe] using he⟩
  · rintro ⟨f, ⟨p, hp, hpe⟩, he⟩
    exact ⟨p, hp, by rw [CoreMemProc.events_eq, hpe]; exact he⟩

/-! ## The clocked profile and coherent states -/

/-- A process of the clocked profile, at index `i` of the design, for any number of clocks: a continuous assign to a
whole declared scalar (function-free; a memory read is evaluated by the route's evaluator, anything else by its compiled
expression, which must be present), or an edge process on either edge of any clock (with or without an asynchronous
reset of either polarity) whose body the view-level executor mirrors with evaluated runtime fuel; a plain
`always` whose event list is one clock edge with an optional reset edge is that edge process (`coreMemEventEdge?`). An
`always_comb`, `always_latch`, `always @*` or `initial` process, and a plain `always` on any other event list, is outside
(refused by name by the structure stage). -/
def CoreMemDesign.ProcOkI (E : CoreMemDesign) (i : Nat) : CoreMemProc → Prop
  | .assign (.ident n) v => LeanModels.Sv.PExpr.hasFunctionCall v = false ∧
      (LeanModels.Sv.PExpr.hasMemoryRead v = false → ∃ c, E.compiledAssigns[i]? = some (some c)) ∧
      (E.scalarWidth? n).isSome = true ∧ n ∉ E.resolvedNets
  | .edge f => f.body.edgeOkB = true
  | .event evs body =>
      match coreMemEventEdge? evs body with
      | some f => f.body.edgeOkB = true
      | none => False
  | _ => False

/-- A process of the single-clock profile: `ProcOkI`, and an edge process is on the rising edge of `clk`. A falling-edge
process is outside it (it is in the instant profile `SeqProfileI`, where `{negedge clk}` is an instant of its own). -/
def CoreMemDesign.ProcOk (E : CoreMemDesign) (clk : String) (i : Nat) : CoreMemProc → Prop
  | .assign (.ident n) v => LeanModels.Sv.PExpr.hasFunctionCall v = false ∧
      (LeanModels.Sv.PExpr.hasMemoryRead v = false → ∃ c, E.compiledAssigns[i]? = some (some c)) ∧
      (E.scalarWidth? n).isSome = true ∧ n ∉ E.resolvedNets
  | .edge f => f.clock = clk ∧ f.edge = .posedge ∧ f.body.edgeOkB = true
  | .event evs body =>
      match coreMemEventEdge? evs body with
      | some f => f.clock = clk ∧ f.edge = .posedge ∧ f.body.edgeOkB = true
      | none => False
  | _ => False

/-- The memories of the clocked profile: distinct names, distinct identities, 4-state elements, none a port of the
design (an input memory would be written by `applyMemoryInputs`, outside this slice). -/
def CoreMemDesign.memOkB (E : CoreMemDesign) : Bool :=
  decide ((E.memories.toList.map fun md => md.source.name).Nodup) &&
    decide ((E.memories.toList.map fun md => md.shape.id).Nodup) &&
    E.memories.toList.all fun md => !md.source.isInput && !md.source.isOutput && !md.shape.twoState

/-- **The clocked profile**, for any number of clocks (the instant view's profile): its memories in the profile
(`memOkB`), the scalar edge view's declarations are the scalar view's, distinct names, every declaration 4-state, every
process `ProcOkI` (edge processes on any clock, either edge). -/
structure CoreMemDesign.SeqProfileI (E : CoreMemDesign) : Prop where
  mems : E.memOkB = true
  base : E.scalarEdge.base = E.scalar
  names : (E.scalar.decls.toList.map Decl.name).Nodup
  four : AllFour E.scalar
  noResolved : E.resolvedNets = []
  procs : ∀ (i : Nat) (p : CoreMemProc), E.processes[i]? = some p → E.ProcOkI i p

/-- An edge process on the rising edge of `clk` (every other process qualifies). -/
def CoreMemProc.OnRise (clk : String) : CoreMemProc → Prop
  | .edge f => f.clock = clk ∧ f.edge = .posedge
  | .event evs body =>
      match coreMemEventEdge? evs body with
      | some f => f.clock = clk ∧ f.edge = .posedge
      | none => True
  | _ => True

/-- **The single-clock profile**: the instant profile at the one clock event `posedge clk` (every edge process on the
rising edge of `clk`; asynchronous resets of either polarity, each an event of its own). -/
structure CoreMemDesign.SeqProfile (E : CoreMemDesign) (clk : String) : Prop extends E.SeqProfileI where
  rise : ∀ p ∈ E.processes.toList, p.OnRise clk

/-- `ProcOk`, decided (the structure stage decides the profile through it, for any number of processes). -/
def CoreMemDesign.procOkB (E : CoreMemDesign) (clk : String) (i : Nat) : CoreMemProc → Bool
  | .assign (.ident n) v => !LeanModels.Sv.PExpr.hasFunctionCall v &&
      (LeanModels.Sv.PExpr.hasMemoryRead v || (match E.compiledAssigns[i]? with
        | some (some _) => true
        | _ => false)) && (E.scalarWidth? n).isSome && !E.resolvedNets.contains n
  | .edge f => f.clock == clk && decide (f.edge = .posedge) && f.body.edgeOkB
  | .event evs body =>
      match coreMemEventEdge? evs body with
      | some f => f.clock == clk && decide (f.edge = .posedge) && f.body.edgeOkB
      | none => false
  | _ => false

theorem CoreMemDesign.procOkB_spec {E : CoreMemDesign} {clk : String} {i : Nat} {p : CoreMemProc}
    (h : E.procOkB clk i p = true) : E.ProcOk clk i p := by
  cases p with
  | assign t v =>
      cases t with
      | ident n =>
          simp only [CoreMemDesign.procOkB, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true] at h
          obtain ⟨⟨⟨h1, h3⟩, h4⟩, h5⟩ := h
          refine And.intro h1 (And.intro (fun hmr => ?_) (And.intro h4 ?_))
          rcases h3 with h3 | h3
          · rw [hmr] at h3; exact absurd h3 (by simp)
          · split at h3
            · rename_i c hc; exact ⟨c, hc⟩
            · simp at h3
          · simpa using h5
      | _ => simp [CoreMemDesign.procOkB] at h
  | edge f =>
      simp only [CoreMemDesign.procOkB, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      exact ⟨h.1.1, h.1.2, h.2⟩
  | primitive _ _ _ => simp [CoreMemDesign.procOkB] at h
  | initial _ => simp [CoreMemDesign.procOkB] at h
  | comb _ => simp [CoreMemDesign.procOkB] at h
  | implicit _ => simp [CoreMemDesign.procOkB] at h
  | latch _ => simp [CoreMemDesign.procOkB] at h
  | event evs body =>
      cases hfe : coreMemEventEdge? evs body with
      | none => simp [CoreMemDesign.procOkB, hfe] at h
      | some f =>
          simp only [CoreMemDesign.procOkB, hfe, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
          simp only [CoreMemDesign.ProcOk, hfe]
          exact ⟨h.1.1, h.1.2, h.2⟩
  | unsupported _ _ => simp [CoreMemDesign.procOkB] at h

/-- Every process from index `i` on is `ProcOk`, decided. -/
def CoreMemDesign.procsOkFrom (E : CoreMemDesign) (clk : String) : Nat → List CoreMemProc → Bool
  | _, [] => true
  | i, p :: ps => E.procOkB clk i p && E.procsOkFrom clk (i + 1) ps

theorem CoreMemDesign.procsOkFrom_spec {E : CoreMemDesign} {clk : String} :
    ∀ (ps : List CoreMemProc) (i : Nat), E.procsOkFrom clk i ps = true →
      ∀ k p, ps[k]? = some p → E.ProcOk clk (i + k) p
  | [], _, _, k, p, hk => by simp at hk
  | q :: ps, i, h, k, p, hk => by
      simp only [CoreMemDesign.procsOkFrom, Bool.and_eq_true] at h
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
          subst hk
          simpa using CoreMemDesign.procOkB_spec h.1
      | succ k =>
          simp only [List.getElem?_cons_succ] at hk
          have := CoreMemDesign.procsOkFrom_spec ps (i + 1) h.2 k p hk
          rwa [show i + 1 + k = i + (k + 1) by omega] at this

/-- A single-clock process is a process of the instant profile on the rising edge of `clk`. -/
theorem CoreMemDesign.ProcOk.toI {E : CoreMemDesign} {clk : String} {i : Nat} {p : CoreMemProc}
    (h : E.ProcOk clk i p) : E.ProcOkI i p ∧ p.OnRise clk := by
  cases p with
  | assign t v =>
      cases t with
      | ident n => exact ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩, trivial⟩
      | _ => exact absurd h (by simp [CoreMemDesign.ProcOk])
  | edge f => exact ⟨h.2.2, h.1, h.2.1⟩
  | event evs body =>
      cases hfe : coreMemEventEdge? evs body with
      | none => exact absurd h (by simp [CoreMemDesign.ProcOk, hfe])
      | some f =>
          simp only [CoreMemDesign.ProcOk, hfe] at h
          simp only [CoreMemDesign.ProcOkI, CoreMemProc.OnRise, hfe]
          exact ⟨h.2.2, h.1, h.2.1⟩
  | _ => exact absurd h (by simp [CoreMemDesign.ProcOk])

/-- An edge process of a design in the single-clock profile is on the rising edge of the clock. -/
theorem CoreMemProc.OnRise.of_edge? {clk : String} {p : CoreMemProc} {f : CoreMemEdge} (h : p.OnRise clk)
    (hf : p.edge? = some f) : f.clock = clk ∧ f.edge = .posedge := by
  cases p with
  | edge g =>
      simp only [CoreMemProc.edge?, Option.some.injEq] at hf
      subst hf
      exact h
  | event evs body =>
      simp only [CoreMemProc.edge?] at hf
      simpa only [CoreMemProc.OnRise, hf] using h
  | _ => exact absurd hf (by simp [CoreMemProc.edge?])

/-- `ProcOkI`, decided. -/
def CoreMemDesign.procOkIB (E : CoreMemDesign) (i : Nat) : CoreMemProc → Bool
  | .assign (.ident n) v => !LeanModels.Sv.PExpr.hasFunctionCall v &&
      (LeanModels.Sv.PExpr.hasMemoryRead v || (match E.compiledAssigns[i]? with
        | some (some _) => true
        | _ => false)) && (E.scalarWidth? n).isSome && !E.resolvedNets.contains n
  | .edge f => f.body.edgeOkB
  | .event evs body =>
      match coreMemEventEdge? evs body with
      | some f => f.body.edgeOkB
      | none => false
  | _ => false

theorem CoreMemDesign.procOkIB_spec {E : CoreMemDesign} {i : Nat} {p : CoreMemProc}
    (h : E.procOkIB i p = true) : E.ProcOkI i p := by
  cases p with
  | assign t v =>
      cases t with
      | ident n =>
          simp only [CoreMemDesign.procOkIB, Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true] at h
          have hfc := h.1.1.1
          have hor := h.1.1.2
          have hw := h.1.2
          have hnet := h.2
          refine And.intro hfc (And.intro (fun hmr => ?_) (And.intro hw ?_))
          rcases hor with hor | hor
          · rw [hmr] at hor; exact absurd hor (by simp)
          · split at hor
            · rename_i c hc; exact ⟨c, hc⟩
            · simp at hor
          · simpa using hnet
      | _ => simp [CoreMemDesign.procOkIB] at h
  | edge f =>
      simp only [CoreMemDesign.procOkIB, Bool.and_eq_true, decide_eq_true_eq] at h
      exact h
  | primitive _ _ _ => simp [CoreMemDesign.procOkIB] at h
  | initial _ => simp [CoreMemDesign.procOkIB] at h
  | comb _ => simp [CoreMemDesign.procOkIB] at h
  | implicit _ => simp [CoreMemDesign.procOkIB] at h
  | latch _ => simp [CoreMemDesign.procOkIB] at h
  | event evs body =>
      cases hfe : coreMemEventEdge? evs body with
      | none => simp [CoreMemDesign.procOkIB, hfe] at h
      | some f =>
          simp only [CoreMemDesign.procOkIB, hfe, Bool.and_eq_true, decide_eq_true_eq] at h
          simp only [CoreMemDesign.ProcOkI, hfe]
          exact h
  | unsupported _ _ => simp [CoreMemDesign.procOkIB] at h

/-- Every process from index `i` on is `ProcOkI`, decided. -/
def CoreMemDesign.procsOkIFrom (E : CoreMemDesign) : Nat → List CoreMemProc → Bool
  | _, [] => true
  | i, p :: ps => E.procOkIB i p && E.procsOkIFrom (i + 1) ps

theorem CoreMemDesign.procsOkIFrom_spec {E : CoreMemDesign} :
    ∀ (ps : List CoreMemProc) (i : Nat), E.procsOkIFrom i ps = true →
      ∀ k p, ps[k]? = some p → E.ProcOkI (i + k) p
  | [], _, _, k, p, hk => by simp at hk
  | q :: ps, i, h, k, p, hk => by
      simp only [CoreMemDesign.procsOkIFrom, Bool.and_eq_true] at h
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
          subst hk
          simpa using CoreMemDesign.procOkIB_spec h.1
      | succ k =>
          simp only [List.getElem?_cons_succ] at hk
          have := CoreMemDesign.procsOkIFrom_spec ps (i + 1) h.2 k p hk
          rwa [show i + 1 + k = i + (k + 1) by omega] at this

/-- The instant profile from its decided parts (how the structure stage proves it). -/
theorem CoreMemDesign.SeqProfileI.of_B {E : CoreMemDesign} (hmo : E.memOkB = true)
    (hb : E.scalarEdge.base = E.scalar) (hn : (E.scalar.decls.toList.map Decl.name).Nodup) (h4 : AllFour E.scalar)
    (hnr : E.resolvedNets = []) (hp : E.procsOkIFrom 0 E.processes.toList = true) : E.SeqProfileI :=
  ⟨hmo, hb, hn, h4, hnr, fun i p hi => by
    have := CoreMemDesign.procsOkIFrom_spec _ 0 hp i p (by rw [Array.getElem?_toList]; exact hi)
    simpa using this⟩

/-- The profile from its decided parts (how the structure stage proves it). -/
theorem CoreMemDesign.SeqProfile.of_B {E : CoreMemDesign} {clk : String} (hmo : E.memOkB = true)
    (hb : E.scalarEdge.base = E.scalar) (hn : (E.scalar.decls.toList.map Decl.name).Nodup) (h4 : AllFour E.scalar)
    (hnr : E.resolvedNets = []) (hp : E.procsOkFrom clk 0 E.processes.toList = true) : E.SeqProfile clk where
  mems := hmo
  base := hb
  names := hn
  four := h4
  noResolved := hnr
  procs := fun i p hi => by
    have := CoreMemDesign.procsOkFrom_spec _ 0 hp i p (by rw [Array.getElem?_toList]; exact hi)
    simpa using (CoreMemDesign.ProcOk.toI this).1
  rise := fun p hmem => by
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hmem
    have hk := CoreMemDesign.procsOkFrom_spec _ 0 hp i p hi
    rw [Nat.zero_add] at hk
    exact (CoreMemDesign.ProcOk.toI hk).2

/-- The memory profile's facts: distinct names, distinct identities, 4-state, not ports. -/
theorem CoreMemDesign.memOkB_spec {E : CoreMemDesign} (h : E.memOkB = true) :
    (E.memories.toList.map fun md => md.source.name).Nodup ∧ (E.memories.toList.map fun md => md.shape.id).Nodup ∧
      ∀ md ∈ E.memories.toList, md.source.isInput = false ∧ md.source.isOutput = false ∧ md.shape.twoState = false := by
  simp only [CoreMemDesign.memOkB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, fun md hmd => ⟨(h.2 md hmd).1.1, (h.2 md hmd).1.2, (h.2 md hmd).2⟩⟩

private theorem eq_of_mem_map_nodup {α β : Type} [DecidableEq β] {f : α → β} :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | d :: l, hnd, a, b, ha, hb, h => by
      simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
      simp only [List.mem_cons] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · rfl
      · exact absurd h.symm (hnd.1 b hb)
      · exact absurd h (hnd.1 a ha)
      · exact eq_of_mem_map_nodup hnd.2 ha hb h

/-- In the memory profile a memory is found by its own name. -/
theorem CoreMemDesign.memDecl?_self {E : CoreMemDesign} (hmo : E.memOkB = true) {md : CoreMemDecl}
    (hmd : md ∈ E.memories.toList) : E.memDecl? md.source.name = some md := by
  have hnd := (CoreMemDesign.memOkB_spec hmo).1
  cases h : E.memDecl? md.source.name with
  | none =>
      simp only [CoreMemDesign.memDecl?, List.find?_eq_none, beq_iff_eq] at h
      exact absurd rfl (h md hmd)
  | some md' =>
      obtain ⟨hmem', hname'⟩ := CoreMemDesign.memDecl?_some h
      rw [eq_of_mem_map_nodup hnd hmem' hmd hname']

/-- A coherent state: the store is its cache's, the cache has one value per declaration, every value of its
declaration's type. -/
structure CoreMemDesign.Coherent (E : CoreMemDesign) (st : CoreMemState) : Prop where
  store : st.scalar = E.scalarStore st.scalarCache
  size : st.scalarCache.size = E.scalar.decls.size
  typed : E.scalar.Typed st.scalar

theorem viewAux_congr_lt {s s' : Store} : ∀ (ds : List Decl) (i : Nat),
    (∀ j, i ≤ j → j < i + ds.length → s { decl := j } = s' { decl := j }) → viewAux s ds i = viewAux s' ds i
  | [], _, _ => rfl
  | dc :: ds, i, h => by
      simp only [viewAux, h i (Nat.le_refl _) (by simp),
        viewAux_congr_lt ds (i + 1) fun j hj hj' => h j (by omega) (by simp at hj' ⊢; omega)]

/-- Two stores that agree on the declared variables have one view. -/
theorem Elab.view_congr_decls {E : Elab} {s s' : Store}
    (h : ∀ j, j < E.decls.size → s { decl := j } = s' { decl := j }) : E.view s = E.view s' :=
  viewAux_congr_lt _ 0 fun j _ hj => h j (by simpa using hj)

theorem Elab.declOf_some {E : Elab} {x : VarId} {dc : Decl} (h : E.declOf x = some dc) :
    x = { decl := x.decl } ∧ x.decl < E.decls.size := by
  unfold Elab.declOf at h
  split at h
  · rename_i hp
    refine ⟨by cases x; simp_all, ?_⟩
    exact (Array.getElem?_eq_some_iff.mp h).1
  · cases h

/-- Two stores that agree on the declared variables are typed together. -/
theorem Elab.typed_congr_decls {E : Elab} {s s' : Store}
    (h : ∀ j, j < E.decls.size → s { decl := j } = s' { decl := j }) (hT : E.Typed s) : E.Typed s' := by
  intro x dc hx
  obtain ⟨hxe, hlt⟩ := Elab.declOf_some hx
  rw [hxe, ← h x.decl hlt, ← hxe]
  exact hT x dc hx

theorem CoreMemDesign.scalarStore_cacheOf (E : CoreMemDesign) (s : Store) :
    ∀ j, j < E.scalar.decls.size → E.scalarStore (E.scalarCacheOf s) { decl := j } = s { decl := j } := by
  intro j hj
  simp [CoreMemDesign.scalarStore, CoreMemDesign.scalarCacheOf, hj]

/-- `normalizeScalar` keeps the view of the store it is given, and is coherent when that store is typed. -/
theorem CoreMemDesign.normalizeScalar_view (E : CoreMemDesign) (st : CoreMemState) (s : Store) :
    E.scalar.view (E.normalizeScalar st s).scalar = E.scalar.view s :=
  Elab.view_congr_decls (E.scalarStore_cacheOf s)

theorem CoreMemDesign.normalizeScalar_coherent (E : CoreMemDesign) (st : CoreMemState) {s : Store}
    (hT : E.scalar.Typed s) : E.Coherent (E.normalizeScalar st s) :=
  { store := rfl
    size := by simp [CoreMemDesign.normalizeScalar, CoreMemDesign.scalarCacheOf]
    typed := Elab.typed_congr_decls (fun j hj => (E.scalarStore_cacheOf s j hj).symm) hT }

/-- `setScalarState` on a coherent state: `SvState.set` on the view, converted to the declaration's type. -/
theorem CoreMemDesign.setScalarState_spec {E : CoreMemDesign} {st : CoreMemState} (hc : E.Coherent st)
    {n : String} {x : VarId} (hx : E.scalar.resolve n = some x) (v : LVec) :
    E.scalar.view (E.setScalarState st n v).scalar =
        SvState.set (E.scalar.view st.scalar) n (Val.ofLVec (st.scalar x).ty v).bits ∧
      E.Coherent (E.setScalarState st n v) := by
  obtain ⟨dc, hdc, -, -, -⟩ := Elab.resolve_some hx
  obtain ⟨hxe, hlt⟩ := Elab.declOf_some hdc
  have hagree : ∀ j, j < E.scalar.decls.size →
      E.scalarStore (st.scalarCache.set! x.decl (Val.ofLVec (st.scalar x).ty v)) { decl := j } =
        (st.scalar.set x (Val.ofLVec (st.scalar x).ty v)) { decl := j } := by
    intro j hj
    have hjc : j < st.scalarCache.size := by rw [hc.size]; exact hj
    by_cases hjx : j = x.decl
    · subst hjx
      rw [hxe]
      simp [CoreMemDesign.scalarStore, Store.set, Array.set!, hjc]
    · have hne : ({ decl := j } : VarId) ≠ x := by
        intro h'; rw [← h'] at hjx; exact hjx rfl
      simp only [CoreMemDesign.scalarStore, Store.set, hne, ↓reduceIte, Array.set!]
      rw [hc.store]
      simp [CoreMemDesign.scalarStore, Array.getElem?_setIfInBounds_ne (Ne.symm hjx)]
  simp only [CoreMemDesign.setScalarState, hx]
  refine ⟨?_, ?_⟩
  · rw [Elab.view_congr_decls hagree, Elab.view_set _ _ hx]
  · exact { store := rfl
            size := by simp [hc.size]
            typed := Elab.typed_congr_decls (fun j hj => (hagree j hj).symm) (hc.typed.set rfl) }

/-- `setScalarState` changes no memory. -/
theorem CoreMemDesign.setScalarState_memory (E : CoreMemDesign) (st : CoreMemState) (n : String) (v : LVec) :
    (E.setScalarState st n v).memory = st.memory := by
  unfold CoreMemDesign.setScalarState
  split <;> rfl

/-- `compactScalar` changes no memory. -/
theorem CoreMemDesign.compactScalar_memory (E : CoreMemDesign) (st : CoreMemState) (w : SvState) :
    (E.compactScalar st w).memory = st.memory := by
  unfold CoreMemDesign.compactScalar
  split <;> rfl

#print axioms CoreMemDesign.setScalarState_spec

/-! ## The continuous-assign settle on views -/

/-- One source-order pass of the continuous assigns on a RAW view (each target set to its value, unconverted, as
`settleAssignAt` threads it): an assign that reads a memory is evaluated by the route's evaluator on the state, whose
view is the materialized `matV raw` (`evalScalarAssignAtView`'s first branch), any other by its compiled expression on
the raw view; edge processes and plain `always` event processes are skipped (as `settleAssignAt` skips them). -/
def CoreMemDesign.settleRaw (E : CoreMemDesign) (mv : MemV) (raw : SvState) (idx : Nat) :
    List CoreMemProc → Res SvState
  | [] => .ok raw
  | .assign (.ident n) value :: rest =>
      if LeanModels.Sv.PExpr.hasMemoryRead value || LeanModels.Sv.PExpr.hasFunctionCall value then
        match E.scalarWidth? n with
        | some w => do
            let x ← E.evalV E.env E.elems (E.matV raw) mv (some w) value
            E.settleRaw mv (SvState.set raw n x) (idx + 1) rest
        | none => .unsupported s!"10.3: continuous target '{n}' is undeclared"
      else
        match E.compiledAssigns[idx]? with
        | some (some c) => do
            let x ← evalPure2 raw c
            E.settleRaw mv (SvState.set raw n x) (idx + 1) rest
        | _ => .unsupported "settleRaw: a continuous assign without its compiled expression"
  | .edge _ :: rest => E.settleRaw mv raw (idx + 1) rest
  | .event _ _ :: rest => E.settleRaw mv raw (idx + 1) rest
  | _ :: _ => .unsupported "settleRaw: a process outside the clocked profile"

/-- **One `settleAssign` on a view**: the pass on the raw view, then the materialization. -/
def CoreMemDesign.settleV (E : CoreMemDesign) (mv : MemV) (v : SvState) : Res SvState := do
  let raw ← E.settleRaw mv v 0 E.processes.toList
  .ok (E.matV raw)

theorem lookup_set' (st : SvState) (n : String) (v : LVec) (m : String) :
    SvState.lookup (SvState.set st n v) m = if n = m then some v else SvState.lookup st m := by
  induction st with
  | nil => simp [SvState.set, SvState.lookup]
  | cons kv rest ih =>
      obtain ⟨k, w⟩ := kv
      by_cases hk : k = n
      · subst hk
        by_cases hkm : k = m <;> simp [SvState.set, SvState.lookup, hkm]
      · have hk' : (k == n) = false := by simpa using hk
        simp only [SvState.set, hk', Bool.false_eq_true, ↓reduceIte, SvState.lookup, ih]
        by_cases hkm : k = m
        · subst hkm; simp [Ne.symm hk]
        · have hkm' : (k == m) = false := by simpa using hkm
          simp [hkm']

private theorem set_map_of_mem {f : Decl → LVec} {n : String} {v : LVec} :
    ∀ (l : List Decl), (l.map Decl.name).Nodup → n ∈ l.map Decl.name →
      SvState.set (l.map fun d => (d.name, f d)) n v =
        l.map fun d => (d.name, if d.name = n then v else f d)
  | [], _, h => by simp at h
  | d :: l, hnd, hmem => by
      simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
      by_cases hd : d.name = n
      · have hrest : ∀ d' ∈ l, d'.name ≠ n := fun d' hd' h => hnd.1 d' hd' (h.trans hd.symm)
        simp only [SvState.set, hd, beq_self_eq_true, ↓reduceIte, List.map_cons, List.cons.injEq, true_and]
        exact (List.map_congr_left fun d' hd' => by simp [hrest d' hd']).symm
      · have hd' : (d.name == n) = false := by simpa using hd
        have hmem' : n ∈ l.map Decl.name := by
          simp only [List.map_cons, List.mem_cons] at hmem
          rcases hmem with h | h
          · exact absurd h.symm hd
          · exact h
        simp only [SvState.set, hd', Bool.false_eq_true, ↓reduceIte, List.map_cons, hd]
        exact congrArg _ (set_map_of_mem l hnd.2 hmem')

private theorem resolveAux_of_nodup {dc : Decl} : ∀ (ds : List Decl) (i k : Nat), (ds.map Decl.name).Nodup →
    ds[k]? = some dc → resolveAux dc.name ds i = some { decl := i + k }
  | [], _, _, _, h => by simp at h
  | d :: ds, i, k, hnd, h => by
      simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
      cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at h
          subst h
          simp only [resolveAux, beq_self_eq_true, ↓reduceIte, Nat.add_zero]
      | succ k =>
          simp only [List.getElem?_cons_succ] at h
          have hne : (d.name == dc.name) = false := by
            have := hnd.1 dc (List.mem_of_getElem? h)
            exact beq_eq_false_iff_ne.mpr (fun h' => this h'.symm)
          simp only [resolveAux, hne, Bool.false_eq_true, ↓reduceIte]
          rw [resolveAux_of_nodup ds (i + 1) k hnd.2 h]
          congr 2
          omega

theorem Val.ext_bits {a b : Val} (hty : a.ty = b.ty) (hb : a.bits = b.bits) : a = b := by
  cases a; cases b; simp_all

/-- The view of `storeFromView raw` is the materialization of `raw`. -/
theorem CoreMemDesign.view_storeFromView (E : CoreMemDesign) (raw : SvState) :
    E.scalar.view (E.storeFromView raw) = E.matV raw := by
  unfold CoreMemDesign.matV Elab.view
  suffices h : ∀ (ds : List Decl) (i : Nat), (∀ k (hk : k < ds.length), E.scalar.decls[i + k]? = some ds[k]) →
      viewAux (E.storeFromView raw) ds i = ds.map (fun dc => (dc.name, (Val.ofLVec (VType.ofDecl dc)
        ((SvState.lookup raw dc.name).getD (declFallback dc))).bits)) by
    exact h _ 0 fun k hk => by simp
  intro ds
  induction ds with
  | nil => intro _ _; rfl
  | cons d ds ih =>
      intro i hi
      have h0 := hi 0 (by simp)
      simp only [Nat.add_zero, List.getElem_cons_zero] at h0
      simp only [List.map_cons, viewAux]
      congr 1
      · simp only [CoreMemDesign.storeFromView, Elab.declOf, h0, declFallback]
      · exact ih (i + 1) fun k hk => by
          have := hi (k + 1) (by simp; omega)
          simpa [Nat.add_assoc, Nat.add_comm 1 k] using this

/-- The materialization of a coherent state's own view is that view. -/
theorem CoreMemDesign.matV_view {E : CoreMemDesign} (hnd : (E.scalar.decls.toList.map Decl.name).Nodup)
    (h4 : AllFour E.scalar) {s : Store} (hT : E.scalar.Typed s) : E.matV (E.scalar.view s) = E.scalar.view s := by
  have hpt : ∀ j, j < E.scalar.decls.size → E.storeFromView (E.scalar.view s) { decl := j } = s { decl := j } := by
    intro j hj
    have hd : E.scalar.decls.toList[j]? = some E.scalar.decls[j] := by simp [hj]
    have hres : E.scalar.resolve E.scalar.decls[j].name = some { decl := j } := by
      simpa [Elab.resolve] using resolveAux_of_nodup E.scalar.decls.toList 0 j hnd hd
    have hdecl : E.scalar.declOf { decl := j } = some E.scalar.decls[j] := by
      simp [Elab.declOf, hj]
    have hty := hT { decl := j } E.scalar.decls[j] hdecl
    have hw : (s { decl := j }).bits.width = E.scalar.decls[j].width := by
      rw [(s { decl := j }).width_eq, hty]; rfl
    have h4j : E.scalar.decls[j].twoState = false := h4 _ (by simp)
    simp only [CoreMemDesign.storeFromView, hdecl, Elab.lookup_view, hres, Option.map_some, Option.getD_some]
    refine Val.ext_bits (by rw [hty]; rfl) ?_
    simp [Val.ofLVec, VType.conv, VType.ofDecl, h4j, LVec.resizeU_of_width hw]
  rw [← E.view_storeFromView]
  exact Elab.view_congr_decls hpt

#print axioms CoreMemDesign.matV_view

theorem CoreMemDesign.typed_storeFromView (E : CoreMemDesign) (raw : SvState) : E.scalar.Typed (E.storeFromView raw) := by
  intro x dc hx
  simp only [CoreMemDesign.storeFromView, hx]
  rfl

theorem CoreMemDesign.scalarWidth?_some {E : CoreMemDesign} {n : String} (h : (E.scalarWidth? n).isSome = true) :
    ∃ x, E.scalar.resolve n = some x := by
  unfold CoreMemDesign.scalarWidth? at h
  split at h
  · rename_i x hx; exact ⟨x, hx⟩
  · simp at h

private theorem eq_of_mem_of_name : ∀ {l : List Decl}, (l.map Decl.name).Nodup → ∀ {a b : Decl},
    a ∈ l → b ∈ l → a.name = b.name → a = b
  | [], _, _, _, ha, _, _ => by simp at ha
  | d :: l, hnd, a, b, ha, hb, h => by
      simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
      simp only [List.mem_cons] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · rfl
      · exact absurd h.symm (hnd.1 b hb)
      · exact absurd h (hnd.1 a ha)
      · exact eq_of_mem_of_name hnd.2 ha hb h

/-- The materialization after one more assign: `SvState.set` of the converted value. -/
theorem CoreMemDesign.matV_set {E : CoreMemDesign} (hnd : (E.scalar.decls.toList.map Decl.name).Nodup)
    {n : String} {x : VarId} {dc : Decl} (hx : E.scalar.resolve n = some x) (hdc : E.scalar.declOf x = some dc)
    (raw : SvState) (val : LVec) :
    E.matV (SvState.set raw n val) = SvState.set (E.matV raw) n (Val.ofLVec (VType.ofDecl dc) val).bits := by
  obtain ⟨dc', hdc', hname, hmem, -⟩ := Elab.resolve_some hx
  rw [hdc] at hdc'
  cases hdc'
  subst hname
  unfold CoreMemDesign.matV
  rw [set_map_of_mem _ hnd (List.mem_map_of_mem (f := Decl.name) hmem)]
  refine List.map_congr_left fun d hd => ?_
  by_cases hdn : d.name = dc.name
  · have hdd : d = dc := eq_of_mem_of_name hnd hd hmem hdn
    subst hdd
    simp
  · have hne : ¬ dc.name = d.name := fun h => hdn h.symm
    simp [lookup_set', hdn, hne]

mutual
/-- **A function-free expression reads no aggregate member**: `hasFunctionCall` classifies an aggregate member read as
outside the function-free fragment, so the route's named aggregate boundary (`hasAggregateMember`, which sends a
continuous assign to the source-shaped evaluator) lies inside the profile's function-free one. -/
theorem seq_noAggregate_of_noCall : ∀ (e : PExpr), LeanModels.Sv.PExpr.hasFunctionCall e = false →
    LeanModels.Sv.PExpr.hasAggregateMember e = false
  | .lit _, _ | .ident _, _ | .paramRef _ _, _ | .genvarRef _, _ | .enumRef _ _ _, _ | .int _, _ | .fill _, _
  | .typeBits _ _, _
  | .unsupported _ _, _ => rfl
  | .functionCall _ _, h => by simp [LeanModels.Sv.PExpr.hasFunctionCall] at h
  | .aggregateMember _ _, h => by simp [LeanModels.Sv.PExpr.hasFunctionCall] at h
  | .unary _ a, h | .resize _ a, h | .signedResize _ a, h | .squash2 _ a, h | .reduce _ a, h
  | .cast _ a, h => by
      have ha := seq_noAggregate_of_noCall a
      simp only [LeanModels.Sv.PExpr.hasFunctionCall] at h
      simp only [LeanModels.Sv.PExpr.hasAggregateMember]
      exact ha h
  | .sysCall _ _, h => by simp [LeanModels.Sv.PExpr.hasFunctionCall] at h
  | .binary _ a b, h | .bitSel a b, h | .repl a b, h => by
      have ha := seq_noAggregate_of_noCall a
      have hb := seq_noAggregate_of_noCall b
      simp only [LeanModels.Sv.PExpr.hasFunctionCall, Bool.or_eq_false_iff] at h
      simp only [LeanModels.Sv.PExpr.hasAggregateMember, Bool.or_eq_false_iff]
      exact ⟨ha h.1, hb h.2⟩
  | .ternary a b c, h | .partSel a b c, h => by
      have ha := seq_noAggregate_of_noCall a
      have hb := seq_noAggregate_of_noCall b
      have hc := seq_noAggregate_of_noCall c
      simp only [LeanModels.Sv.PExpr.hasFunctionCall, Bool.or_eq_false_iff] at h
      simp only [LeanModels.Sv.PExpr.hasAggregateMember, Bool.or_eq_false_iff]
      exact ⟨⟨ha h.1.1, hb h.1.2⟩, hc h.2⟩
  | .concat xs, h | .arrayElem _ xs, h => by
      have hx := seq_noAggregate_of_noCallList xs
      simp only [LeanModels.Sv.PExpr.hasFunctionCall] at h
      simp only [LeanModels.Sv.PExpr.hasAggregateMember]
      exact hx h
  | .arrayPart _ xs _ a b, h => by
      have hx := seq_noAggregate_of_noCallList xs
      have ha := seq_noAggregate_of_noCall a
      have hb := seq_noAggregate_of_noCall b
      simp only [LeanModels.Sv.PExpr.hasFunctionCall, Bool.or_eq_false_iff] at h
      simp only [LeanModels.Sv.PExpr.hasAggregateMember, Bool.or_eq_false_iff]
      exact ⟨⟨hx h.1.1, ha h.1.2⟩, hb h.2⟩

/-- `seq_noAggregate_of_noCall` of a list. -/
theorem seq_noAggregate_of_noCallList : ∀ (es : List PExpr), LeanModels.Sv.PExpr.hasFunctionCallList es = false →
    LeanModels.Sv.PExpr.hasAggregateMemberList es = false
  | [], _ => rfl
  | e :: es, h => by
      have he := seq_noAggregate_of_noCall e
      have hes := seq_noAggregate_of_noCallList es
      simp only [LeanModels.Sv.PExpr.hasFunctionCallList, Bool.or_eq_false_iff] at h
      simp only [LeanModels.Sv.PExpr.hasAggregateMemberList, Bool.or_eq_false_iff]
      exact ⟨he h.1, hes h.2⟩
end

/-! A function-free expression also cannot contain the runtime `$test$plusargs`
    system call.  `evalScalarAssignAtView` uses this fact to select the same
    source-shaped evaluator branch as `settleRaw`. -/
mutual
theorem seq_noTestPlusargs_of_noCall : ∀ (e : PExpr), LeanModels.Sv.PExpr.hasFunctionCall e = false →
    LeanModels.Sv.PExpr.hasTestPlusargs e = false
  | .lit _, _ | .ident _, _ | .paramRef _ _, _ | .genvarRef _, _ | .enumRef _ _ _, _ | .int _, _ | .fill _, _
  | .typeBits _ _, _ | .unsupported _ _, _ => rfl
  | .functionCall _ _, h => by simp [LeanModels.Sv.PExpr.hasFunctionCall] at h
  | .aggregateMember _ _, h => by simp [LeanModels.Sv.PExpr.hasFunctionCall] at h
  | .sysCall _ _, h => by simp [LeanModels.Sv.PExpr.hasFunctionCall] at h
  | .unary _ a, h | .resize _ a, h | .signedResize _ a, h | .squash2 _ a, h | .reduce _ a, h
  | .cast _ a, h => by
      exact seq_noTestPlusargs_of_noCall a (by simpa [LeanModels.Sv.PExpr.hasFunctionCall] using h)
  | .binary _ a b, h | .bitSel a b, h | .repl a b, h => by
      simp only [LeanModels.Sv.PExpr.hasFunctionCall, Bool.or_eq_false_iff] at h
      simp only [LeanModels.Sv.PExpr.hasTestPlusargs, Bool.or_eq_false_iff]
      exact ⟨seq_noTestPlusargs_of_noCall a h.1, seq_noTestPlusargs_of_noCall b h.2⟩
  | .ternary a b c, h | .partSel a b c, h => by
      simp only [LeanModels.Sv.PExpr.hasFunctionCall, Bool.or_eq_false_iff] at h
      simp only [LeanModels.Sv.PExpr.hasTestPlusargs, Bool.or_eq_false_iff]
      exact ⟨⟨seq_noTestPlusargs_of_noCall a h.1.1,
        seq_noTestPlusargs_of_noCall b h.1.2⟩,
        seq_noTestPlusargs_of_noCall c h.2⟩
  | .concat xs, h | .arrayElem _ xs, h => by
      exact seq_noTestPlusargs_of_noCallList xs
        (by simpa [LeanModels.Sv.PExpr.hasFunctionCall] using h)
  | .arrayPart _ xs _ a b, h => by
      simp only [LeanModels.Sv.PExpr.hasFunctionCall, Bool.or_eq_false_iff] at h
      simp only [LeanModels.Sv.PExpr.hasTestPlusargs, Bool.or_eq_false_iff]
      exact ⟨⟨seq_noTestPlusargs_of_noCallList xs h.1.1,
        seq_noTestPlusargs_of_noCall a h.1.2⟩,
        seq_noTestPlusargs_of_noCall b h.2⟩

theorem seq_noTestPlusargs_of_noCallList : ∀ (es : List PExpr),
    LeanModels.Sv.PExpr.hasFunctionCallList es = false →
    LeanModels.Sv.PExpr.hasTestPlusargsList es = false
  | [], _ => rfl
  | e :: es, h => by
      simp only [LeanModels.Sv.PExpr.hasFunctionCallList, Bool.or_eq_false_iff] at h
      simp only [LeanModels.Sv.PExpr.hasTestPlusargsList, Bool.or_eq_false_iff]
      exact ⟨seq_noTestPlusargs_of_noCall e h.1,
        seq_noTestPlusargs_of_noCallList es h.2⟩
end

/-- **`settleAssignAt` on the clocked profile is `settleRaw`**, keeping coherence, the memory and the materialized
view. -/
theorem CoreMemDesign.settleAssignAt_seq {E : CoreMemDesign} (hP : E.SeqProfileI) :
    ∀ (procs : List CoreMemProc) (idx : Nat), (∀ k p, procs[k]? = some p → E.processes[idx + k]? = some p) →
    ∀ (st : CoreMemState) (raw raw' : SvState), E.Coherent st → E.MemCoherent st.memory →
      E.scalar.view st.scalar = E.matV raw → E.settleRaw (E.memOf st.memory) raw idx procs = .ok raw' →
      ∃ st', E.settleAssignAt E.env E.elems st raw idx procs = .ok (st', raw') ∧ E.Coherent st' ∧
        st'.memory = st.memory ∧ E.scalar.view st'.scalar = E.matV raw'
  | [], idx, _, st, raw, raw', hc, _, hv, hs => by
      simp only [CoreMemDesign.settleRaw, Res.ok.injEq] at hs
      subst hs
      exact ⟨st, rfl, hc, rfl, hv⟩
  | p :: rest, idx, hidx, st, raw, raw', hc, hmc, hv, hs => by
      have hp : E.processes[idx]? = some p := by simpa using hidx 0 p rfl
      have hrest : ∀ k q, rest[k]? = some q → E.processes[idx + 1 + k]? = some q := by
        intro k q hq
        have := hidx (k + 1) q (by simpa using hq)
        rwa [show idx + (k + 1) = idx + 1 + k by omega] at this
      have hok := hP.procs idx p hp
      cases p with
      | assign target value =>
          cases target with
          | ident n =>
              obtain ⟨hfc, hcomp, hw, hnet⟩ := hok
              obtain ⟨xid, hxid⟩ := CoreMemDesign.scalarWidth?_some hw
              obtain ⟨dc, hdc, hname, -, -⟩ := Elab.resolve_some hxid
              have hsw : E.scalarWidth? n = some dc.width := by
                simp [CoreMemDesign.scalarWidth?, hxid, hdc]
              have hty : (st.scalar xid).ty = VType.ofDecl dc := hc.typed xid dc hdc
              -- the value the route assigns, and the raw view it threads
              have hstep : ∀ x, E.settleRaw (E.memOf st.memory) (SvState.set raw n x) (idx + 1) rest = .ok raw' →
                  E.evalScalarAssignAtView E.env E.elems st raw (some dc.width) idx value = .ok x →
                  ∃ st', E.settleAssignAt E.env E.elems st raw idx (.assign (.ident n) value :: rest) = .ok (st', raw') ∧
                    E.Coherent st' ∧ st'.memory = st.memory ∧ E.scalar.view st'.scalar = E.matV raw' := by
                intro x hs' hx
                have hset := CoreMemDesign.setScalarState_spec hc hxid x
                have hv' : E.scalar.view (E.setScalarState st n x).scalar = E.matV (SvState.set raw n x) := by
                  rw [hset.1, hv, CoreMemDesign.matV_set hP.names hxid hdc, hty]
                have hmem := E.setScalarState_memory st n x
                obtain ⟨st', hrun, hc', hm', hv''⟩ := CoreMemDesign.settleAssignAt_seq hP rest (idx + 1) hrest _ _ _
                  hset.2 (by rw [hmem]; exact hmc) hv' (by rw [hmem]; exact hs')
                refine ⟨st', ?_, hc', by rw [hm', hmem], hv''⟩
                simp only [CoreMemDesign.settleAssignAt, hsw, Res.ok_bind, hx]
                simpa [hnet] using hrun
              by_cases hmr : LeanModels.Sv.PExpr.hasMemoryRead value = true
              · simp only [CoreMemDesign.settleRaw, hmr, Bool.true_or, ↓reduceIte, hsw, Res.bind_eq_ok] at hs
                obtain ⟨x, hx, hs⟩ := hs
                refine hstep x hs ?_
                simp only [CoreMemDesign.evalScalarAssignAtView, hmr, hfc, Bool.and_false,
                  Bool.true_or, ↓reduceIte, seq_noTestPlusargs_of_noCall value hfc]
                rw [CoreMemDesign.evalExpr_eq hmc E.env (some dc.width) value hfc, hv]
                exact hx
              · rw [Bool.not_eq_true] at hmr
                obtain ⟨c, hc'⟩ := hcomp hmr
                simp only [CoreMemDesign.settleRaw, hmr, hfc, Bool.or_false, Bool.false_eq_true, ↓reduceIte, hc',
                  Res.bind_eq_ok] at hs
                obtain ⟨x, hx, hs⟩ := hs
                refine hstep x hs ?_
                simp only [CoreMemDesign.evalScalarAssignAtView, hmr, hfc, seq_noAggregate_of_noCall value hfc,
                  Bool.or_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte,
                  seq_noTestPlusargs_of_noCall value hfc, hc']
                exact hx
          | _ => exact absurd hok (by simp [CoreMemDesign.ProcOkI])
      | edge f =>
          simp only [CoreMemDesign.settleRaw] at hs
          obtain ⟨st', hrun, hc', hm', hv'⟩ :=
            CoreMemDesign.settleAssignAt_seq hP rest (idx + 1) hrest st raw raw' hc hmc hv hs
          exact ⟨st', by simpa [CoreMemDesign.settleAssignAt] using hrun, hc', hm', hv'⟩
      | primitive _ _ _ => exact absurd hok (by simp [CoreMemDesign.ProcOkI])
      | initial _ => exact absurd hok (by simp [CoreMemDesign.ProcOkI])
      | comb _ => exact absurd hok (by simp [CoreMemDesign.ProcOkI])
      | implicit _ => exact absurd hok (by simp [CoreMemDesign.ProcOkI])
      | latch _ => exact absurd hok (by simp [CoreMemDesign.ProcOkI])
      | event evs body =>
          simp only [CoreMemDesign.settleRaw] at hs
          obtain ⟨st', hrun, hc', hm', hv'⟩ :=
            CoreMemDesign.settleAssignAt_seq hP rest (idx + 1) hrest st raw raw' hc hmc hv hs
          exact ⟨st', by simpa [CoreMemDesign.settleAssignAt] using hrun, hc', hm', hv'⟩
      | unsupported _ _ => exact absurd hok (by simp [CoreMemDesign.ProcOkI])

/-- `compactScalar` after a settle pass: the materialized view, coherent. -/
theorem CoreMemDesign.compactScalar_spec {E : CoreMemDesign} {st : CoreMemState} (hc : E.Coherent st)
    {raw : SvState} (hv : E.scalar.view st.scalar = E.matV raw) :
    E.scalar.view (E.compactScalar st raw).scalar = E.matV raw ∧ E.Coherent (E.compactScalar st raw) := by
  unfold CoreMemDesign.compactScalar
  split
  · exact ⟨hv, hc⟩
  · refine ⟨?_, E.normalizeScalar_coherent st (E.typed_storeFromView raw)⟩
    show E.scalar.view (E.normalizeScalar st (E.storeFromView raw)).scalar = _
    rw [E.normalizeScalar_view, E.view_storeFromView]

/-- **One `settleAssign` of the route is `settleV` on the view**, on the clocked profile, from a coherent state. -/
theorem CoreMemDesign.settleAssign_seq {E : CoreMemDesign} (hP : E.SeqProfileI)
    {st : CoreMemState} (hc : E.Coherent st) (hmc : E.MemCoherent st.memory) {v' : SvState}
    (hv : E.settleV (E.memOf st.memory) (E.scalar.view st.scalar) = .ok v') :
    ∃ st', E.settleAssign E.env E.elems st E.processes.toList = .ok st' ∧ E.scalar.view st'.scalar = v' ∧
      E.Coherent st' ∧ st'.memory = st.memory := by
  simp only [CoreMemDesign.settleV, Res.bind_eq_ok, Res.ok.injEq] at hv
  obtain ⟨raw', hs, rfl⟩ := hv
  obtain ⟨st', hrun, hc', hm', hv'⟩ := CoreMemDesign.settleAssignAt_seq hP E.processes.toList 0
    (fun k p hk => by simpa using hk) st _ raw' hc hmc (CoreMemDesign.matV_view hP.names hP.four hc.typed).symm hs
  obtain ⟨hvc, hcc⟩ := CoreMemDesign.compactScalar_spec hc' hv'
  have hreset : E.resetResolvedNets st = st := by
    simp [CoreMemDesign.resetResolvedNets, hP.noResolved]
  have hsettle : E.settleAssign E.env E.elems st E.processes.toList =
      .ok (E.compactScalar st' raw') := by
    simp [CoreMemDesign.settleAssign, hreset, hrun]
  refine ⟨E.compactScalar st' raw', hsettle, hvc, hcc, ?_⟩
  rw [E.compactScalar_memory, hm']

#print axioms CoreMemDesign.settleAssign_seq

/-! ## The edge-body executor on views refines the route's -/

/-- `setScalarState` on a coherent state is `setV` on its view, and stays coherent. -/
theorem CoreMemDesign.setV_spec {E : CoreMemDesign} {st : CoreMemState} (hc : E.Coherent st) {n : String}
    {x : VarId} (hx : E.scalar.resolve n = some x) (v : LVec) :
    E.scalar.view (E.setScalarState st n v).scalar = E.setV (E.scalar.view st.scalar) n v ∧
      E.Coherent (E.setScalarState st n v) := by
  obtain ⟨dc, hdc, -, -, -⟩ := Elab.resolve_some hx
  have hty : (st.scalar x).ty = VType.ofDecl dc := hc.typed x dc hdc
  obtain ⟨h1, h2⟩ := CoreMemDesign.setScalarState_spec hc hx v
  refine ⟨?_, h2⟩
  rw [h1, hty]
  simp [CoreMemDesign.setV, hx, hdc]

/-- `compactScalar` on a coherent state: the materialized view, coherent. -/
theorem CoreMemDesign.compactScalar_view {E : CoreMemDesign} (hnd : (E.scalar.decls.toList.map Decl.name).Nodup)
    (h4 : AllFour E.scalar) {st : CoreMemState} (hc : E.Coherent st) (w : SvState) :
    E.scalar.view (E.compactScalar st w).scalar = E.matV w ∧ E.Coherent (E.compactScalar st w) := by
  unfold CoreMemDesign.compactScalar
  split
  · rename_i h
    refine ⟨?_, hc⟩
    rw [← h, CoreMemDesign.matV_view hnd h4 hc.typed]
  · refine ⟨?_, E.normalizeScalar_coherent st (E.typed_storeFromView w)⟩
    show E.scalar.view (E.normalizeScalar st (E.storeFromView w)).scalar = _
    rw [E.normalizeScalar_view, E.view_storeFromView]

/-- `writeScalarLhs2` on a coherent state is `writeLhsV` on its view (and changes no memory). -/
theorem CoreMemDesign.writeLhs_V {E : CoreMemDesign} (hnd : (E.scalar.decls.toList.map Decl.name).Nodup)
    (h4 : AllFour E.scalar) {st : CoreMemState} (hc : E.Coherent st) (lhs : Lhs2) (x : LVec) {v' : SvState}
    (h : E.writeLhsV (E.scalar.view st.scalar) lhs x = .ok v') :
    ∃ st', E.writeScalarLhs2 st lhs x = .ok st' ∧ E.scalar.view st'.scalar = v' ∧ E.Coherent st' ∧
      st'.memory = st.memory := by
  cases lhs
  case concat parts =>
    simp only [CoreMemDesign.writeLhsV, Res.bind_eq_ok, Res.ok.injEq] at h
    obtain ⟨ws, hws, w', hw', rfl⟩ := h
    obtain ⟨h1, h2⟩ := CoreMemDesign.compactScalar_view hnd h4 hc w'
    exact ⟨_, by simp [CoreMemDesign.writeScalarLhs2, hws, hw'], h1, h2, E.compactScalar_memory st w'⟩
  all_goals
    simp only [CoreMemDesign.writeLhsV, Res.bind_eq_ok] at h
    obtain ⟨⟨name, window⟩, hr, hw⟩ := h
    dsimp only at hw
    cases window with
    | none =>
        simp only [Res.ok.injEq] at hw
        subst hw
        exact ⟨st, by simp [CoreMemDesign.writeScalarLhs2, hr], rfl, hc, rfl⟩
    | some lw =>
        obtain ⟨lo, width⟩ := lw
        cases hx : E.scalar.resolve name with
        | none => simp [hx] at hw
        | some xid =>
            simp only [hx, Res.ok.injEq] at hw
            subst hw
            have hl : SvState.lookup (E.scalar.view st.scalar) name = some (st.scalar xid).bits := by
              rw [Elab.lookup_view, hx]; rfl
            obtain ⟨h1, h2⟩ := CoreMemDesign.setV_spec hc hx ((st.scalar xid).bits.insertAt lo (x.resizeU width))
            exact ⟨_, by simp [CoreMemDesign.writeScalarLhs2, hr, hx], by rw [h1, hl]; rfl, h2,
              E.setScalarState_memory _ _ _⟩

/-- The route's pattern-list evaluator is `evalListV` on the view (coherent memory, function-free patterns). -/
theorem CoreMemDesign.evalMemExprList_eq {E : CoreMemDesign} {st : CoreMemState} (hmc : E.MemCoherent st.memory) (env : IEnv) :
    ∀ (ps : List PExpr), LeanModels.Sv.PExpr.hasFunctionCallList ps = false →
      evalMemExprList E env E.elems st ps = E.evalListV env E.elems (E.scalar.view st.scalar) (E.memOf st.memory) ps
  | [], _ => by simp [evalMemExprList, CoreMemDesign.evalListV]
  | p :: ps, h => by
      simp only [LeanModels.Sv.PExpr.hasFunctionCallList, Bool.or_eq_false_iff] at h
      simp only [evalMemExprList, CoreMemDesign.evalListV, CoreMemDesign.evalExpr_eq hmc env none p h.1,
        CoreMemDesign.evalMemExprList_eq hmc env ps h.2]

/-- The route's qualified-case hit count is `caseHitsV` on the view. -/
theorem CoreMemDesign.caseHits_eq {E : CoreMemDesign} {st : CoreMemState} (hmc : E.MemCoherent st.memory)
    (env : IEnv) (sv : LVec) (mode : CaseMode) :
    ∀ (items : List (List PExpr × PStmt)), PStmt.itemsEdgeOkB items = true →
      coreMemCaseHits E env E.elems st sv mode items =
        E.caseHitsV env (E.scalar.view st.scalar) (E.memOf st.memory) sv mode items
  | [], _ => by simp [coreMemCaseHits, CoreMemDesign.caseHitsV]
  | (ps, b) :: rest, h => by
      simp only [PStmt.itemsEdgeOkB, Bool.and_eq_true, Bool.not_eq_true'] at h
      simp only [coreMemCaseHits, CoreMemDesign.caseHitsV, CoreMemDesign.evalMemExprList_eq hmc env ps h.1.1,
        CoreMemDesign.caseHits_eq hmc env sv mode rest h.2]

/-! ## Memory records -/

/-- The route's memory record of a view-level record (the memory's identity for its name). -/
def CoreMemDesign.memRec (E : CoreMemDesign) (r : String × Int × LVec) : MemNbaRecord :=
  { id := ((E.memDecl? r.1).map fun md => md.shape.id).getD {}, label := r.2.1, value := r.2.2 }

/-- A view-level record names a memory, at a label in its range, with a value of its element width. -/
def CoreMemDesign.RecOk (E : CoreMemDesign) (r : String × Int × LVec) : Prop :=
  ∃ md, E.memDecl? r.1 = some md ∧ md.shape.inRange r.2.1 ∧ r.2.2.width = md.shape.elemWidth

/-- The records of an issued element write are well formed and are the route's. -/
theorem CoreMemDesign.issueV_spec {E : CoreMemDesign} {n : String} {md : CoreMemDecl}
    (hmd : E.memDecl? n = some md) (sg : Bool) (idx x : LVec) :
    (∀ r ∈ md.issueV sg idx x, E.RecOk r) ∧
      (md.issueV sg idx x).map E.memRec = match md.shape.index? sg idx with
        | some k => [{ id := md.shape.id, label := k, value := md.shape.convert x }]
        | none => [] := by
  obtain ⟨-, hname⟩ := CoreMemDesign.memDecl?_some hmd
  have hmd' : E.memDecl? md.source.name = some md := by rw [hname]; exact hmd
  unfold CoreMemDecl.issueV
  cases hk : md.shape.index? sg idx with
  | none => simp [memIss]
  | some k =>
      refine ⟨?_, by simp [memIss, CoreMemDesign.memRec, hmd']⟩
      intro r hr
      simp only [memIss, List.mem_singleton] at hr
      subst hr
      exact ⟨md, hmd', MemShape.index?_inRange hk, MemShape.width_convert _ _⟩

theorem CoreMemDesign.execStmtFuel_nil_map (E : CoreMemDesign) : ([] : MemQV).map E.memRec = [] := rfl

mutual

/-- **A loop body of the profile leaves the view as it was**: it issues nonblocking updates only. -/
theorem CoreMemDesign.execV_loopBody {E : CoreMemDesign} (env : IEnv) (v : SvState) (mv : MemV) :
    ∀ (b : PStmt) (r : ExecV), b.loopBodyB = true → E.execV env v mv b = .ok r → r.1 = v
  | .nbaAssign t e, r, _, h => by
      simp only [CoreMemDesign.execV] at h
      split at h
      · simp at h
      · simp only [Res.bind_eq_ok, Res.ok.injEq] at h
        obtain ⟨x, -, rfl⟩ := h
        rfl
  | .nbaAssignL lhs e, r, _, h => by
      cases lhs with
      | ident t =>
          simp only [CoreMemDesign.execV] at h
          split at h
          · simp at h
          · simp only [Res.bind_eq_ok, Res.ok.injEq] at h
            obtain ⟨x, -, rfl⟩ := h
            rfl
      | arrayElem name indices =>
          simp only [CoreMemDesign.execV] at h
          split at h
          · simp only [Res.bind_eq_ok, Res.ok.injEq] at h
            obtain ⟨lw, -, x, -, ws, -, rfl⟩ := h
            rfl
          · split at h
            · simp only [Res.bind_eq_ok, Res.ok.injEq] at h
              obtain ⟨x, -, iv, -, rfl⟩ := h
              rfl
            · simp at h
      | _ =>
          simp only [CoreMemDesign.execV, Res.bind_eq_ok, Res.ok.injEq] at h
          obtain ⟨lw, -, x, -, ws, -, rfl⟩ := h
          rfl
  | .ifStmt c y n, r, hb, h => by
      simp only [PStmt.loopBodyB, Bool.and_eq_true] at hb
      simp only [CoreMemDesign.execV, Res.bind_eq_ok] at h
      obtain ⟨cv, -, h⟩ := h
      split at h
      · exact CoreMemDesign.execV_loopBody env v mv y r hb.1 h
      · cases n with
        | none =>
            simp only [CoreMemDesign.execOptV, Res.ok.injEq] at h
            subst h
            rfl
        | some s =>
            simp only [CoreMemDesign.execOptV] at h
            exact CoreMemDesign.execV_loopBody env v mv s r (by simpa [PStmt.optLoopBodyB] using hb.2) h
  | .block body, r, hb, h => by
      simp only [PStmt.loopBodyB] at hb
      simp only [CoreMemDesign.execV] at h
      exact CoreMemDesign.execListV_loopBody env v mv body r hb h
  | .caseStmt subject items d mode check, r, hb, h => by
      simp only [PStmt.loopBodyB, Bool.and_eq_true] at hb
      have hdflt : ∀ r', E.execOptV env v mv d = .ok r' → r'.1 = v := by
        intro r' hr
        cases d with
        | none =>
            simp only [CoreMemDesign.execOptV, Res.ok.injEq] at hr
            subst hr
            rfl
        | some s =>
            simp only [CoreMemDesign.execOptV] at hr
            exact CoreMemDesign.execV_loopBody env v mv s r' (by simpa [PStmt.optLoopBodyB] using hb.2) hr
      have hitems : ∀ sv res, E.execItemsV env v mv sv mode items (E.execOptV env v mv d) = .ok res → res.1 = v :=
        fun sv res hres => CoreMemDesign.execItemsV_loopBody env v mv sv mode items _ res hb.1 hdflt hres
      simp only [CoreMemDesign.execV, Res.bind_eq_ok] at h
      obtain ⟨sv, -, h⟩ := h
      cases check
      case none => exact hitems sv r h
      all_goals
        simp only [Res.bind_eq_ok] at h
        obtain ⟨n, -, h⟩ := h
        split at h
        · exact hitems sv r h
        · simp at h
  | .blockingAssign .., _, hb, _ => by simp [PStmt.loopBodyB] at hb
  | .blockingAssignL .., _, hb, _ => by simp [PStmt.loopBodyB] at hb
  | .localDecl .., _, hb, _ => by simp [PStmt.loopBodyB] at hb
  | .automaticDecl .., _, hb, _ => by simp [PStmt.loopBodyB] at hb
  | .forLoop .., _, hb, _ => by simp [PStmt.loopBodyB] at hb
  | .unsupported .., _, hb, _ => by simp [PStmt.loopBodyB] at hb

/-- The list form of `execV_loopBody`. -/
theorem CoreMemDesign.execListV_loopBody {E : CoreMemDesign} (env : IEnv) (v : SvState) (mv : MemV) :
    ∀ (bs : List PStmt) (r : ExecV), PStmt.listLoopBodyB bs = true → E.execListV env v mv bs = .ok r → r.1 = v
  | [], r, _, h => by
      simp only [CoreMemDesign.execListV, Res.ok.injEq] at h
      subst h
      rfl
  | s :: ss, r, hb, h => by
      simp only [PStmt.listLoopBodyB, Bool.and_eq_true] at hb
      simp only [CoreMemDesign.execListV, Res.bind_eq_ok, Res.ok.injEq] at h
      obtain ⟨a, h1, b, h2, rfl⟩ := h
      have ha := CoreMemDesign.execV_loopBody env v mv s a hb.1 h1
      have hb' := CoreMemDesign.execListV_loopBody env a.1 mv ss b hb.2 h2
      show b.1 = v
      rw [hb', ha]

/-- The arms of a `case`, `execV_loopBody`'s form. -/
theorem CoreMemDesign.execItemsV_loopBody {E : CoreMemDesign} (env : IEnv) (v : SvState) (mv : MemV) (sv : LVec)
    (mode : CaseMode) :
    ∀ (items : List (List PExpr × PStmt)) (dflt : Res ExecV) (res : ExecV), PStmt.itemsLoopBodyB items = true →
      (∀ r, dflt = .ok r → r.1 = v) → E.execItemsV env v mv sv mode items dflt = .ok res → res.1 = v
  | [], dflt, res, _, hd, h => by
      simp only [CoreMemDesign.execItemsV] at h
      exact hd res h
  | (ps, b) :: rest, dflt, res, hb, hd, h => by
      simp only [PStmt.itemsLoopBodyB, Bool.and_eq_true] at hb
      simp only [CoreMemDesign.execItemsV, Res.bind_eq_ok] at h
      obtain ⟨vals, -, h⟩ := h
      split at h
      · exact CoreMemDesign.execV_loopBody env v mv b res hb.1 h
      · exact CoreMemDesign.execItemsV_loopBody env v mv sv mode rest dflt res hb.2 hd h

end

/-- **The loop fold's refinement**, from the body's: when every run of the body under the iterator's binding leaves
the view as it was and is refined by the route's executor at every fuel from `nb` on, the fold over a value list
(`execLoopV`) is refined by the route's `execLoopValuesFuel` at every fuel from `length values + 1 + nb` on (one unit
per iteration): the route threads its state, whose view and memory no iteration changes; the queues append. Induction
over the value list; the list itself is arbitrary (never unrolled). -/
theorem CoreMemDesign.execLoopValuesFuel_V {E : CoreMemDesign} (env : IEnv) (it : String) (body : PStmt) (nb : Nat)
    (hview : ∀ (i : Int) (v : SvState) (mv : MemV) (r : ExecV), E.execV (env.bindVal it i) v mv body = .ok r → r.1 = v)
    (hbody : ∀ (i : Int) (fuel : Nat) (st : CoreMemState) (v' : SvState) (q : NbaQueue2) (mq : MemQV),
      E.Coherent st → E.MemCoherent st.memory → nb ≤ fuel →
      E.execV (env.bindVal it i) (E.scalar.view st.scalar) (E.memOf st.memory) body = .ok (v', q, mq) →
      ∃ st', E.execStmtFuel (env.bindVal it i) E.elems st [] fuel body = .ok ⟨st', q, mq.map E.memRec, []⟩ ∧
        E.scalar.view st'.scalar = v' ∧ E.Coherent st' ∧ st'.memory = st.memory ∧ ∀ r ∈ mq, E.RecOk r) :
    ∀ (values : List Int) (fuel : Nat) (st : CoreMemState) (v' : SvState) (q : NbaQueue2) (mq : MemQV),
      E.Coherent st → E.MemCoherent st.memory → values.length + 1 + nb ≤ fuel →
      execLoopV (E.scalar.view st.scalar)
        (fun i => E.execV (env.bindVal it i) (E.scalar.view st.scalar) (E.memOf st.memory) body) values =
          .ok (v', q, mq) →
      ∃ st', E.execLoopValuesFuel env E.elems st [] fuel values body it = .ok ⟨st', q, mq.map E.memRec, []⟩ ∧
        E.scalar.view st'.scalar = v' ∧ E.Coherent st' ∧ st'.memory = st.memory ∧ ∀ r ∈ mq, E.RecOk r
  | [], fuel, st, v', q, mq, hc, _, hf, hv => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [execLoopV, Res.ok.injEq, Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      exact ⟨st, by simp [CoreMemDesign.execLoopValuesFuel], rfl, hc, rfl, by simp⟩
  | i :: rest, fuel, st, v', q, mq, hc, hmc, hf, hv => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      simp only [List.length_cons] at hf
      simp only [execLoopV, Res.bind_eq_ok, Res.ok.injEq] at hv
      obtain ⟨⟨v1, a, ma⟩, h1, ⟨v2, b, mb⟩, h2, hq⟩ := hv
      simp only [Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl, rfl⟩ := hq
      have e1 : v1 = E.scalar.view st.scalar := hview i _ _ _ h1
      have e2 : v2 = E.scalar.view st.scalar := execLoopV_fst h2
      obtain ⟨st1, hs1, hv1, hc1, hm1, hr1⟩ := hbody i f st v1 a ma hc hmc (by omega) h1
      obtain ⟨st2, hs2, hv2, hc2, hm2, hr2⟩ := CoreMemDesign.execLoopValuesFuel_V env it body nb hview hbody rest f
        st1 v2 b mb hc1 (by rw [hm1]; exact hmc) (by omega) (by rw [hv1, e1, hm1]; exact h2)
      refine ⟨st2, by simp [CoreMemDesign.execLoopValuesFuel, hs1, hs2, CoreMemExec.append], by rw [hv2, e2], hc2,
        by rw [hm2, hm1], fun r hr => ?_⟩
      rcases List.mem_append.mp hr with hr | hr
      · exact hr1 r hr
      · exact hr2 r hr

mutual

/-- **THE EDGE-BODY REFINEMENT**: from a coherent state with a coherent memory, when the view-level executor gives
`(v', q, mq)` the route's edge-body executor (at every fuel from the body's need on) leaves a coherent state whose view
is `v'` and whose memory is unchanged, and issues exactly `q` and the route's records of `mq` (each well formed). -/
theorem CoreMemDesign.execStmtFuel_V {E : CoreMemDesign}
    (hnd : (E.scalar.decls.toList.map Decl.name).Nodup) (h4 : AllFour E.scalar) :
    ∀ (b : PStmt) (env : IEnv) (fuel : Nat) (st : CoreMemState) (v' : SvState) (q : NbaQueue2) (mq : MemQV), E.Coherent st →
      E.MemCoherent st.memory → b.edgeOkB = true → b.need env ≤ fuel →
      E.execV env (E.scalar.view st.scalar) (E.memOf st.memory) b = .ok (v', q, mq) →
      ∃ st', E.execStmtFuel env E.elems st [] fuel b = .ok ⟨st', q, mq.map E.memRec, []⟩ ∧
        E.scalar.view st'.scalar = v' ∧ E.Coherent st' ∧ st'.memory = st.memory ∧ ∀ r ∈ mq, E.RecOk r
  | .nbaAssign t e, env, fuel, st, v', q, mq, hc, hmc, hb, hf, hv => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [PStmt.need] at hf; omega⟩
      simp only [PStmt.edgeOkB, Bool.not_eq_true'] at hb
      simp only [CoreMemDesign.execV] at hv
      cases hw : E.scalarTarget t with
      | none => simp [hw] at hv
      | some w =>
          simp only [hw, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
          obtain ⟨x, hx, rfl, rfl, rfl⟩ := hv
          refine ⟨st, ?_, rfl, hc, rfl, by simp⟩
          simp [CoreMemDesign.execStmtFuel, CoreMemExec.withLocals, hw, CoreMemDesign.evalExpr_eq hmc env (some w) e hb, CoreMemDesign.evalExprLocals_eq_evalV hmc env E.elems (some w) e hb, hx,
            CoreMemDesign.issueTarget, CoreMemExec.fromQueue]
  | .nbaAssignL lhs e, env, fuel, st, v', q, mq, hc, hmc, hb, hf, hv => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [PStmt.need] at hf; omega⟩
      simp only [PStmt.edgeOkB, Bool.and_eq_true, Bool.not_eq_true'] at hb
      obtain ⟨hb, hbt⟩ := hb
      cases lhs with
      | ident t =>
          simp only [CoreMemDesign.execV] at hv
          cases hw : E.scalarTarget t with
          | none => simp [hw] at hv
          | some w =>
              simp only [hw, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
              obtain ⟨x, hx, rfl, rfl, rfl⟩ := hv
              refine ⟨st, ?_, rfl, hc, rfl, by simp⟩
              simp [CoreMemDesign.execStmtFuel, CoreMemExec.withLocals, hw, CoreMemDesign.evalExpr_eq hmc env (some w) e hb, CoreMemDesign.evalExprLocals_eq_evalV hmc env E.elems (some w) e hb, hx,
                CoreMemDesign.issueTarget, CoreMemExec.fromQueue]
      | arrayElem name indices =>
          cases hmd : E.memDecl? name with
          | none =>
              simp only [CoreMemDesign.execV, hmd, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
              obtain ⟨⟨l, w⟩, hl, x, hx, ws, hws, rfl, rfl, rfl⟩ := hv
              dsimp only at hx hws
              refine ⟨st, ?_, rfl, hc, rfl, by simp⟩
              simp [CoreMemDesign.execStmtFuel, CoreMemExec.withLocals, hmd, hl, CoreMemDesign.evalExpr_eq hmc env (some w) e hb, CoreMemDesign.evalExprLocals_eq_evalV hmc env E.elems (some w) e hb, hx,
                CoreMemDesign.issueScalarTarget, hws, CoreMemExec.fromQueue]
          | some md =>
              cases indices with
              | nil => simp [CoreMemDesign.execV, hmd] at hv
              | cons index more =>
                  cases more with
                  | cons _ _ => simp [CoreMemDesign.execV, hmd] at hv
                  | nil =>
                      simp only [PLhs.hasCall, LeanModels.Sv.PExpr.hasFunctionCallList, Bool.or_false] at hbt
                      simp only [CoreMemDesign.execV, hmd, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
                      obtain ⟨x, hx, iv, hiv, rfl, rfl, rfl⟩ := hv
                      obtain ⟨hmem, -⟩ := CoreMemDesign.memDecl?_some hmd
                      obtain ⟨blk, hblk, -, hs, -⟩ := hmc.blocks md hmem
                      obtain ⟨hrec, hmap⟩ := CoreMemDesign.issueV_spec hmd index.signedCast iv x
                      have hidx : E.evalIndex env E.elems st index = .ok iv := by
                        rw [CoreMemDesign.evalIndex_eq hmc env index hbt]; exact hiv
                      refine ⟨st, ?_, rfl, hc, rfl, hrec⟩
                      have hex : E.evalExpr env E.elems st (some md.shape.elemWidth) e = .ok x := by
                        rw [CoreMemDesign.evalExpr_eq hmc env _ e hb]; exact hx
                      simp only [CoreMemDesign.execStmtFuel, hmd, Res.bind_eq_ok,
                        CoreMemDesign.evalExprLocals_eq_evalV hmc env E.elems
                          (some md.shape.elemWidth) e hb, hx, CoreMemExec.withLocals,
                        CoreMemDesign.issueTarget, hidx, MemState.issueNba, hblk, hs]
                      cases hshape : md.shape.index? index.signedCast iv with
                      | none =>
                          have hmap' := hmap
                          rw [hshape] at hmap'
                          simp only [CoreMemExec.fromQueue, CoreMemExec.withLocals, Res.ok.injEq,
                            Prod.mk.injEq]
                          simpa [PExpr.signedCast] using hmap'.symm
                      | some k =>
                          have hmap' := hmap
                          rw [hshape] at hmap'
                          simp only [CoreMemExec.fromQueue, CoreMemExec.withLocals, Res.ok.injEq,
                            Prod.mk.injEq]
                          simpa [PExpr.signedCast] using hmap'.symm
      | bitSel name idx =>
          simp only [CoreMemDesign.execV, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
          obtain ⟨⟨l, w⟩, hl, x, hx, ws, hws, rfl, rfl, rfl⟩ := hv
          dsimp only at hx hws
          refine ⟨st, ?_, rfl, hc, rfl, by simp⟩
          simp [CoreMemDesign.execStmtFuel, CoreMemExec.withLocals, hl, CoreMemDesign.evalExpr_eq hmc env (some w) e hb, CoreMemDesign.evalExprLocals_eq_evalV hmc env E.elems (some w) e hb, hx,
            CoreMemDesign.issueScalarTarget, hws, CoreMemExec.fromQueue]
      | partSel name a b =>
          simp only [CoreMemDesign.execV, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
          obtain ⟨⟨l, w⟩, hl, x, hx, ws, hws, rfl, rfl, rfl⟩ := hv
          dsimp only at hx hws
          refine ⟨st, ?_, rfl, hc, rfl, by simp⟩
          simp [CoreMemDesign.execStmtFuel, CoreMemExec.withLocals, hl, CoreMemDesign.evalExpr_eq hmc env (some w) e hb, CoreMemDesign.evalExprLocals_eq_evalV hmc env E.elems (some w) e hb, hx,
            CoreMemDesign.issueScalarTarget, hws, CoreMemExec.fromQueue]
      | concat parts =>
          simp only [CoreMemDesign.execV, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
          obtain ⟨⟨l, w⟩, hl, x, hx, ws, hws, rfl, rfl, rfl⟩ := hv
          dsimp only at hx hws
          refine ⟨st, ?_, rfl, hc, rfl, by simp⟩
          simp [CoreMemDesign.execStmtFuel, CoreMemExec.withLocals, hl, CoreMemDesign.evalExpr_eq hmc env (some w) e hb, CoreMemDesign.evalExprLocals_eq_evalV hmc env E.elems (some w) e hb, hx,
            CoreMemDesign.issueScalarTarget, hws, CoreMemExec.fromQueue]
      | arrayPart name indices mode a b =>
          simp only [CoreMemDesign.execV, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
          obtain ⟨⟨l, w⟩, hl, x, hx, ws, hws, rfl, rfl, rfl⟩ := hv
          dsimp only at hx hws
          refine ⟨st, ?_, rfl, hc, rfl, by simp⟩
          simp [CoreMemDesign.execStmtFuel, CoreMemExec.withLocals, hl, CoreMemDesign.evalExpr_eq hmc env (some w) e hb, CoreMemDesign.evalExprLocals_eq_evalV hmc env E.elems (some w) e hb, hx,
            CoreMemDesign.issueScalarTarget, hws, CoreMemExec.fromQueue]
      | aggregateMember _ _ =>
          simp [PLhs.hasCall] at hbt
      | arrayBitSel _ _ _ =>
          simp [PLhs.hasCall] at hbt
  | .blockingAssign n e, env, fuel, st, v', q, mq, hc, hmc, hb, hf, hv => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [PStmt.need] at hf; omega⟩
      simp only [PStmt.edgeOkB, Bool.not_eq_true'] at hb
      simp only [CoreMemDesign.execV] at hv
      cases hw : E.scalarTarget n with
      | none => simp [hw] at hv
      | some w =>
          simp only [hw, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
          obtain ⟨x, hx, rfl, rfl, rfl⟩ := hv
          obtain ⟨xid, hxid⟩ := CoreMemDesign.scalarWidth?_some (E := E) (n := n) (by
            have hw' : E.scalarWidth? n = some w := hw
            simp [hw'])
          obtain ⟨h1, h2⟩ := CoreMemDesign.setV_spec hc hxid x
          refine ⟨_, ?_, h1, h2, E.setScalarState_memory _ _ _, by simp⟩
          simp [CoreMemDesign.execStmtFuel, CoreMemExec.withLocals, CoreMemDesign.execBlockingIdentLocal,
            CoreMemDesign.execBlockingTarget, hw,
            CoreMemDesign.evalExpr_eq hmc env (some w) e hb,
            CoreMemDesign.evalExpr_eq hmc env (some w) e hb, CoreMemDesign.evalExprLocals_eq_evalV hmc env E.elems (some w) e hb, hx]
  | .blockingAssignL lhs e, env, fuel, st, v', q, mq, hc, hmc, hb, hf, hv => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [PStmt.need] at hf; omega⟩
      simp only [PStmt.edgeOkB, Bool.and_eq_true, Bool.not_eq_true'] at hb
      obtain ⟨hb, hbt⟩ := hb
      cases lhs with
      | ident n =>
          simp only [CoreMemDesign.execV] at hv
          cases hw : E.scalarTarget n with
          | none => simp [hw] at hv
          | some w =>
              simp only [hw, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
              obtain ⟨x, hx, rfl, rfl, rfl⟩ := hv
              obtain ⟨xid, hxid⟩ := CoreMemDesign.scalarWidth?_some (E := E) (n := n) (by
                have hw' : E.scalarWidth? n = some w := hw
                simp [hw'])
              obtain ⟨h1, h2⟩ := CoreMemDesign.setV_spec hc hxid x
              refine ⟨_, ?_, h1, h2, E.setScalarState_memory _ _ _, by simp⟩
              simp [CoreMemDesign.execStmtFuel, CoreMemExec.withLocals, CoreMemDesign.execBlockingIdentLocal,
                CoreMemDesign.execBlockingTarget, hw,
                CoreMemDesign.evalExpr_eq hmc env (some w) e hb,
                CoreMemDesign.evalExpr_eq hmc env (some w) e hb, CoreMemDesign.evalExprLocals_eq_evalV hmc env E.elems (some w) e hb, hx]
      | arrayElem name indices =>
          cases hmd : E.memDecl? name with
          | some md => simp [CoreMemDesign.execV, hmd] at hv
          | none =>
              simp only [CoreMemDesign.execV, hmd, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
              obtain ⟨⟨l, w⟩, hl, x, hx, w', hw', rfl, rfl, rfl⟩ := hv
              dsimp only at hx hw'
              obtain ⟨st', hs', hv'', hc', hm'⟩ := CoreMemDesign.writeLhs_V hnd h4 hc l x hw'
              refine ⟨st', ?_, hv'', hc', hm', by simp⟩
              simp [CoreMemDesign.execStmtFuel, CoreMemExec.withLocals, CoreMemDesign.execBlockingTarget, hmd,
                CoreMemDesign.execScalarTarget, hl, CoreMemDesign.evalExpr_eq hmc env (some w) e hb,
                CoreMemDesign.evalExpr_eq hmc env (some w) e hb, CoreMemDesign.evalExprLocals_eq_evalV hmc env E.elems (some w) e hb, hx, hs']
      | bitSel name idx =>
          simp only [CoreMemDesign.execV, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
          obtain ⟨⟨l, w⟩, hl, x, hx, w', hw', rfl, rfl, rfl⟩ := hv
          dsimp only at hx hw'
          obtain ⟨st', hs', hv'', hc', hm'⟩ := CoreMemDesign.writeLhs_V hnd h4 hc l x hw'
          refine ⟨st', ?_, hv'', hc', hm', by simp⟩
          simp [CoreMemDesign.execStmtFuel, CoreMemExec.withLocals, CoreMemDesign.execBlockingTarget, CoreMemDesign.execScalarTarget,
            hl, CoreMemDesign.evalExpr_eq hmc env (some w) e hb,
            CoreMemDesign.evalExpr_eq hmc env (some w) e hb, CoreMemDesign.evalExprLocals_eq_evalV hmc env E.elems (some w) e hb, hx, hs']
      | partSel name a b =>
          simp only [CoreMemDesign.execV, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
          obtain ⟨⟨l, w⟩, hl, x, hx, w', hw', rfl, rfl, rfl⟩ := hv
          dsimp only at hx hw'
          obtain ⟨st', hs', hv'', hc', hm'⟩ := CoreMemDesign.writeLhs_V hnd h4 hc l x hw'
          refine ⟨st', ?_, hv'', hc', hm', by simp⟩
          simp [CoreMemDesign.execStmtFuel, CoreMemExec.withLocals, CoreMemDesign.execBlockingTarget, CoreMemDesign.execScalarTarget,
            hl, CoreMemDesign.evalExpr_eq hmc env (some w) e hb,
            CoreMemDesign.evalExpr_eq hmc env (some w) e hb, CoreMemDesign.evalExprLocals_eq_evalV hmc env E.elems (some w) e hb, hx, hs']
      | concat parts =>
          simp only [CoreMemDesign.execV, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
          obtain ⟨⟨l, w⟩, hl, x, hx, w', hw', rfl, rfl, rfl⟩ := hv
          dsimp only at hx hw'
          obtain ⟨st', hs', hv'', hc', hm'⟩ := CoreMemDesign.writeLhs_V hnd h4 hc l x hw'
          refine ⟨st', ?_, hv'', hc', hm', by simp⟩
          simp [CoreMemDesign.execStmtFuel, CoreMemExec.withLocals, CoreMemDesign.execBlockingTarget, CoreMemDesign.execScalarTarget,
            hl, CoreMemDesign.evalExpr_eq hmc env (some w) e hb,
            CoreMemDesign.evalExpr_eq hmc env (some w) e hb, CoreMemDesign.evalExprLocals_eq_evalV hmc env E.elems (some w) e hb, hx, hs']
      | arrayPart name indices mode a b =>
          simp only [CoreMemDesign.execV, Res.bind_eq_ok, Res.ok.injEq, Prod.mk.injEq] at hv
          obtain ⟨⟨l, w⟩, hl, x, hx, w', hw', rfl, rfl, rfl⟩ := hv
          dsimp only at hx hw'
          obtain ⟨st', hs', hv'', hc', hm'⟩ := CoreMemDesign.writeLhs_V hnd h4 hc l x hw'
          refine ⟨st', ?_, hv'', hc', hm', by simp⟩
          simp [CoreMemDesign.execStmtFuel, CoreMemExec.withLocals, CoreMemDesign.execBlockingTarget, CoreMemDesign.execScalarTarget,
            hl, CoreMemDesign.evalExpr_eq hmc env (some w) e hb,
            CoreMemDesign.evalExpr_eq hmc env (some w) e hb, CoreMemDesign.evalExprLocals_eq_evalV hmc env E.elems (some w) e hb, hx, hs']
      | aggregateMember _ _ =>
          simp [PLhs.hasCall] at hbt
      | arrayBitSel _ _ _ =>
          simp [PLhs.hasCall] at hbt
  | .ifStmt c y n, env, fuel, st, v', q, mq, hc, hmc, hb, hf, hv => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [PStmt.need] at hf; omega⟩
      simp only [PStmt.edgeOkB, Bool.and_eq_true, Bool.not_eq_true'] at hb
      obtain ⟨⟨hcf, hy⟩, hn⟩ := hb
      simp only [PStmt.need] at hf
      have hfy : y.need env ≤ f := by omega
      have hfn : PStmt.optNeed env n ≤ f := by omega
      simp only [CoreMemDesign.execV, Res.bind_eq_ok] at hv
      obtain ⟨cv, hcv, hv⟩ := hv
      have hcv' : E.evalExpr env E.elems st (some 1) c = .ok cv := by
        rw [CoreMemDesign.evalExpr_eq hmc env (some 1) c hcf]; exact hcv
      by_cases hct : cv.condTrue = true
      · simp only [hct, ↓reduceIte] at hv
        obtain ⟨st', hs, hv', hc', hm', hr⟩ := CoreMemDesign.execStmtFuel_V hnd h4 y env f st v' q mq hc hmc hy hfy hv
        refine ⟨st', ?_, hv', hc', hm', hr⟩
        simp only [CoreMemDesign.execStmtFuel]
        rw [CoreMemDesign.evalExprLocals_eq_evalV hmc env E.elems (some 1) c hcf]
        simp [hcv, hct, hs]
      · simp only [hct, Bool.false_eq_true, ↓reduceIte] at hv
        cases n with
        | none =>
            simp only [CoreMemDesign.execOptV, Res.ok.injEq, Prod.mk.injEq] at hv
            obtain ⟨rfl, rfl, rfl⟩ := hv
            refine ⟨st, ?_, rfl, hc, rfl, by simp⟩
            simp only [CoreMemDesign.execStmtFuel]
            rw [CoreMemDesign.evalExprLocals_eq_evalV hmc env E.elems (some 1) c hcf]
            simp [hcv, hct]
        | some s =>
            simp only [PStmt.optEdgeOkB] at hn
            simp only [PStmt.optNeed] at hfn
            simp only [CoreMemDesign.execOptV] at hv
            obtain ⟨st', hs, hv', hc', hm', hr⟩ := CoreMemDesign.execStmtFuel_V hnd h4 s env f st v' q mq hc hmc hn hfn hv
            refine ⟨st', ?_, hv', hc', hm', hr⟩
            simp only [CoreMemDesign.execStmtFuel]
            rw [CoreMemDesign.evalExprLocals_eq_evalV hmc env E.elems (some 1) c hcf]
            simp [hcv, hct, hs]
  | .block body, env, fuel, st, v', q, mq, hc, hmc, hb, hf, hv => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [PStmt.need] at hf; omega⟩
      simp only [PStmt.edgeOkB] at hb
      simp only [PStmt.need] at hf
      simp only [CoreMemDesign.execV] at hv
      obtain ⟨st', hs, hv', hc', hm', hr⟩ :=
        CoreMemDesign.execStmtsFuel_V hnd h4 body env f st v' q mq hc hmc hb (by omega) hv
      exact ⟨st', by simp only [CoreMemDesign.execStmtFuel]; exact hs, hv', hc', hm', hr⟩
  | .caseStmt subject items d mode check, env, fuel, st, v', q, mq, hc, hmc, hb, hf, hv => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [PStmt.need] at hf; omega⟩
      simp only [PStmt.edgeOkB, Bool.and_eq_true, Bool.not_eq_true'] at hb
      obtain ⟨⟨hs, hi⟩, hd⟩ := hb
      simp only [PStmt.need] at hf
      have hfi : PStmt.itemsNeed env items ≤ f := by omega
      have hfd : PStmt.optNeed env d ≤ f := by omega
      have hdef : ∀ s, d = some s → E.execV env (E.scalar.view st.scalar) (E.memOf st.memory) s = .ok (v', q, mq) →
          ∃ st', E.execStmtFuel env E.elems st [] f s = .ok ⟨st', q, mq.map E.memRec, []⟩ ∧
            E.scalar.view st'.scalar = v' ∧ E.Coherent st' ∧ st'.memory = st.memory ∧ ∀ r ∈ mq, E.RecOk r := by
        intro s hds hx
        subst hds
        simp only [PStmt.optEdgeOkB] at hd
        simp only [PStmt.optNeed] at hfd
        exact CoreMemDesign.execStmtFuel_V hnd h4 s env f st v' q mq hc hmc hd hfd hx
      simp only [CoreMemDesign.execV, Res.bind_eq_ok] at hv
      obtain ⟨sv, hsv, hv⟩ := hv
      have hsv' : E.evalExpr env E.elems st none subject = .ok sv := by
        rw [CoreMemDesign.evalExpr_eq hmc env none subject hs]; exact hsv
      have hsvLoc : E.evalExprLocals env E.elems st none [] subject = .ok sv := by
        rw [CoreMemDesign.evalExprLocals_eq_evalV hmc env E.elems none subject hs]; exact hsv
      have hrun : E.execItemsV env (E.scalar.view st.scalar) (E.memOf st.memory) sv mode items
          (E.execOptV env (E.scalar.view st.scalar) (E.memOf st.memory) d) = .ok (v', q, mq) →
          ∃ sel st', coreMemSelectCase E env E.elems st sv mode items d = .ok sel ∧
            ((sel = none ∧ st' = st ∧ q = [] ∧ mq = []) ∨
              ∃ body, sel = some body ∧ E.execStmtFuel env E.elems st [] f body = .ok ⟨st', q, mq.map E.memRec, []⟩) ∧
            E.scalar.view st'.scalar = v' ∧ E.Coherent st' ∧ st'.memory = st.memory ∧ ∀ r ∈ mq, E.RecOk r := by
        intro hr
        rcases CoreMemDesign.execItems_V hnd h4 sv mode items env f st _ _ hc hmc hi hfi hr with
          ⟨body, st', hsel, hs, hv1, hc1, hm1, hr1⟩ | ⟨hsel, hdf⟩
        · exact ⟨some body, st', hsel d, Or.inr ⟨body, rfl, hs⟩, hv1, hc1, hm1, hr1⟩
        · cases d with
          | none =>
              simp only [CoreMemDesign.execOptV, Res.ok.injEq, Prod.mk.injEq] at hdf
              obtain ⟨rfl, rfl, rfl⟩ := hdf
              exact ⟨none, st, hsel none, Or.inl ⟨rfl, rfl, rfl, rfl⟩, rfl, hc, rfl, by simp⟩
          | some s =>
              simp only [CoreMemDesign.execOptV] at hdf
              obtain ⟨st', hs, hv1, hc1, hm1, hr1⟩ := hdef s rfl hdf
              exact ⟨some s, st', hsel (some s), Or.inr ⟨s, rfl, hs⟩, hv1, hc1, hm1, hr1⟩
      cases check
      case none =>
          obtain ⟨sel, st', hsel, hcase, h2, h3, h4', h5⟩ := hrun hv
          refine ⟨st', ?_, h2, h3, h4', h5⟩
          rcases hcase with ⟨rfl, rfl, rfl, rfl⟩ | ⟨body, rfl, hs⟩
          · simp [CoreMemDesign.execStmtFuel, CoreMemExec.withLocals, hsv', hsvLoc, hsel]
          · simp [CoreMemDesign.execStmtFuel, CoreMemExec.withLocals, hsv', hsvLoc, hsel, hs]
      all_goals
          simp only [Res.bind_eq_ok] at hv
          obtain ⟨n, hn, hv⟩ := hv
          have hn' : coreMemCaseHits E env E.elems st sv mode items = .ok n := by
            rw [CoreMemDesign.caseHits_eq hmc env sv mode items hi]; exact hn
          split at hv
          · rename_i hok
            obtain ⟨sel, st', hsel, hcase, h2, h3, h4', h5⟩ := hrun hv
            refine ⟨st', ?_, h2, h3, h4', h5⟩
            rcases hcase with ⟨rfl, rfl, rfl, rfl⟩ | ⟨body, rfl, hs⟩
            · simp [CoreMemDesign.execStmtFuel, CoreMemExec.withLocals, hsv', hsvLoc, hn', hok, hsel]
            · simp [CoreMemDesign.execStmtFuel, CoreMemExec.withLocals, hsv', hsvLoc, hn', hok, hsel, hs]
          · simp at hv
  | .forLoop it init cond step body, env, fuel, st, v', q, mq, hc, hmc, hb, hf, hv => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [PStmt.need] at hf; omega⟩
      simp only [PStmt.edgeOkB, Bool.and_eq_true] at hb
      obtain ⟨hbe, hlf⟩ := hb
      simp only [PStmt.need] at hf
      simp only [CoreMemDesign.execV, hlf, ↓reduceIte] at hv
      cases hvals : forValues2 env it init cond step with
      | timeout => simp [hvals] at hv
      | unsupported e => simp [hvals] at hv
      | ok values =>
          simp only [hvals] at hv
          have htr : loopTrips env it init cond step = values.length := by simp [loopTrips, hvals]
          rw [htr] at hf
          obtain ⟨st', hs, hrest⟩ := CoreMemDesign.execLoopValuesFuel_V env it body (PStmt.need env body)
            (fun i v1 mv1 r1 h1 => CoreMemDesign.execV_loopBody (env.bindVal it i) v1 mv1 body r1 hlf h1)
            (fun i fuel' st1 v1 q1 mq1 hc1 hmc1 hf1 h1 =>
              CoreMemDesign.execStmtFuel_V hnd h4 body (env.bindVal it i) fuel' st1 v1 q1 mq1 hc1 hmc1 hbe
                (by rw [PStmt.need_env (env.bindVal it i) env body hlf]; exact hf1) h1)
            values f st v' q mq hc hmc (by omega) hv
          exact ⟨st', by simp only [CoreMemDesign.execStmtFuel, hvals]; exact hs, hrest⟩
  | .unsupported .., _, _, _, _, _, _, _, _, hb, _, _ => by simp [PStmt.edgeOkB] at hb

/-- The list form of `execStmtFuel_V`: the route's `execStmtsFuel` threads the state as `execListV` threads the view. -/
theorem CoreMemDesign.execStmtsFuel_V {E : CoreMemDesign}
    (hnd : (E.scalar.decls.toList.map Decl.name).Nodup) (h4 : AllFour E.scalar) :
    ∀ (bs : List PStmt) (env : IEnv) (fuel : Nat) (st : CoreMemState) (v' : SvState) (q : NbaQueue2) (mq : MemQV), E.Coherent st →
      E.MemCoherent st.memory → PStmt.listEdgeOkB bs = true → PStmt.listNeed env bs ≤ fuel →
      E.execListV env (E.scalar.view st.scalar) (E.memOf st.memory) bs = .ok (v', q, mq) →
      ∃ st', E.execStmtsFuel env E.elems st [] fuel bs = .ok ⟨st', q, mq.map E.memRec, []⟩ ∧
        E.scalar.view st'.scalar = v' ∧ E.Coherent st' ∧ st'.memory = st.memory ∧ ∀ r ∈ mq, E.RecOk r
  | [], env, fuel, st, v', q, mq, hc, _, _, hf, hv => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [PStmt.listNeed] at hf; omega⟩
      simp only [CoreMemDesign.execListV, Res.ok.injEq, Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      exact ⟨st, rfl, rfl, hc, rfl, by simp⟩
  | s :: ss, env, fuel, st, v', q, mq, hc, hmc, hb, hf, hv => by
      obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp [PStmt.listNeed] at hf; omega⟩
      simp only [PStmt.listEdgeOkB, Bool.and_eq_true] at hb
      simp only [PStmt.listNeed] at hf
      simp only [CoreMemDesign.execListV, Res.bind_eq_ok, Res.ok.injEq] at hv
      obtain ⟨⟨v1, a, ma⟩, h1, ⟨v2, b, mb⟩, h2, hq⟩ := hv
      simp only [Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl, rfl⟩ := hq
      obtain ⟨st1, hs1, hv1, hc1, hm1, hr1⟩ := CoreMemDesign.execStmtFuel_V hnd h4 s env f st v1 a ma hc hmc hb.1 (by omega) h1
      obtain ⟨st2, hs2, hv2, hc2, hm2, hr2⟩ := CoreMemDesign.execStmtsFuel_V hnd h4 ss env f st1 v2 b mb hc1
        (by rw [hm1]; exact hmc) hb.2 (by omega) (by rw [hv1, hm1]; exact h2)
      refine ⟨st2, by simp [CoreMemDesign.execStmtsFuel, hs1, hs2, CoreMemExec.append], hv2, hc2, by rw [hm2, hm1],
        fun r hr => ?_⟩
      rcases List.mem_append.mp hr with hr | hr
      · exact hr1 r hr
      · exact hr2 r hr

/-- The arms of a `case`: when the view-level search finds an arm, the route's selection finds the same arm and its
run lands on the same view and queues; when it finds none, the route's selection falls to the default and the result
is the default's. -/
theorem CoreMemDesign.execItems_V {E : CoreMemDesign}
    (hnd : (E.scalar.decls.toList.map Decl.name).Nodup) (h4 : AllFour E.scalar) (sv : LVec) (mode : CaseMode) :
    ∀ (items : List (List PExpr × PStmt)) (env : IEnv) (fuel : Nat) (st : CoreMemState) (dflt : Res ExecV) (res : ExecV),
      E.Coherent st → E.MemCoherent st.memory → PStmt.itemsEdgeOkB items = true → PStmt.itemsNeed env items ≤ fuel →
      E.execItemsV env (E.scalar.view st.scalar) (E.memOf st.memory) sv mode items dflt = .ok res →
      (∃ body st', (∀ d, coreMemSelectCase E env E.elems st sv mode items d = .ok (some body)) ∧
          E.execStmtFuel env E.elems st [] fuel body = .ok ⟨st', res.2.1, res.2.2.map E.memRec, []⟩ ∧
          E.scalar.view st'.scalar = res.1 ∧ E.Coherent st' ∧ st'.memory = st.memory ∧ ∀ r ∈ res.2.2, E.RecOk r) ∨
        ((∀ d, coreMemSelectCase E env E.elems st sv mode items d = .ok d) ∧ dflt = .ok res)
  | [], env, fuel, st, dflt, res, hc, _, _, _, hv => by
      simp only [CoreMemDesign.execItemsV] at hv
      exact Or.inr ⟨fun d => rfl, hv⟩
  | (ps, b) :: rest, env, fuel, st, dflt, res, hc, hmc, hb, hf, hv => by
      simp only [PStmt.itemsEdgeOkB, Bool.and_eq_true, Bool.not_eq_true'] at hb
      simp only [PStmt.itemsNeed] at hf
      simp only [CoreMemDesign.execItemsV, Res.bind_eq_ok] at hv
      obtain ⟨vals, hvals, hv⟩ := hv
      have hpe : evalMemExprList E env E.elems st ps = .ok vals := by
        rw [CoreMemDesign.evalMemExprList_eq hmc env ps hb.1.1]; exact hvals
      by_cases hhit : vals.any (fun value => caseHit mode sv value) = true
      · simp only [hhit, ↓reduceIte] at hv
        obtain ⟨v', q, mq⟩ := res
        obtain ⟨st', hs, hv', hc', hm', hr'⟩ :=
          CoreMemDesign.execStmtFuel_V hnd h4 b env fuel st v' q mq hc hmc hb.1.2 (by omega) hv
        exact Or.inl ⟨b, st', fun d => by simp only [coreMemSelectCase, hpe, Res.ok_bind, hhit, ↓reduceIte], hs,
          hv', hc', hm', hr'⟩
      · rw [Bool.not_eq_true] at hhit
        simp only [hhit, Bool.false_eq_true, ↓reduceIte] at hv
        rcases CoreMemDesign.execItems_V hnd h4 sv mode rest env fuel st dflt res hc hmc hb.2 (by omega) hv with
          ⟨body, st', hsel, hs, hv', hc', hm', hr'⟩ | ⟨hsel, hdf⟩
        · exact Or.inl ⟨body, st', fun d => by
            simp only [coreMemSelectCase, hpe, Res.ok_bind, hhit, Bool.false_eq_true, ↓reduceIte, hsel d],
            hs, hv', hc', hm', hr'⟩
        · exact Or.inr ⟨fun d => by
            simp only [coreMemSelectCase, hpe, Res.ok_bind, hhit, Bool.false_eq_true, ↓reduceIte, hsel d], hdf⟩

end

#print axioms CoreMemDesign.execStmtFuel_V

/-! ## The commit of memory records: the write equation on the route's memory state -/

private theorem find_filter_ne {xs : List (MemId × MemBlock)} {id id' : MemId} (h : id' ≠ id) :
    ((xs.filter fun p => p.1 != id).find? fun p => p.1 == id') = xs.find? fun p => p.1 == id' := by
  induction xs with
  | nil => rfl
  | cons p ps ih =>
      obtain ⟨a, b⟩ := p
      by_cases hp : a = id
      · subst hp
        have hq : (a == id') = false := by simpa using Ne.symm h
        simp [List.filter_cons, List.find?_cons, hq, ih]
      · have hp' : (a != id) = true := by simpa using hp
        by_cases hq : a = id'
        · subst hq; simp [List.filter_cons, List.find?_cons, hp']
        · have hq' : (a == id') = false := by simpa using hq
          simp [List.filter_cons, List.find?_cons, hp', hq', ih]

/-- `MemState.setId`'s lookup (its tables are the route's own `upsert`/`findEntry`, unfolded definitionally). -/
theorem MemState.setId_lookupId (m : MemState) (id : MemId) (b : MemBlock) (id' : MemId) :
    (m.setId id b).lookupId id' = if id' = id then some b else (m.entries.find? fun p => p.1 == id').map (·.2) := by
  have h1 : (m.setId id b).lookupId id' =
      ((((id, b) :: m.entries.filter fun p => p.1 != id).find? fun p => p.1 == id').map (·.2)) := rfl
  rw [h1]
  by_cases h : id' = id
  · subst h; simp [List.find?_cons]
  · have hne : (id == id') = false := by simpa using Ne.symm h
    simp [List.find?_cons, hne, h, find_filter_ne h]

/-- `MemState.setId`'s entry table, found by identity. -/
theorem MemState.setId_find (m : MemState) (id : MemId) (b : MemBlock) (id' : MemId) :
    (((m.setId id b).entries.find? fun p => p.1 == id').map (·.2)) =
      if id' = id then some b else (m.entries.find? fun p => p.1 == id').map (·.2) := by
  have h1 : (m.setId id b).entries = (id, b) :: m.entries.filter fun p => p.1 != id := rfl
  rw [h1]
  by_cases h : id' = id
  · subst h; simp [List.find?_cons]
  · have hne : (id == id') = false := by simpa using Ne.symm h
    simp [List.find?_cons, hne, h, find_filter_ne h]

/-- A write keeps a block's shape. -/
theorem MemBlock.write_shape (m : MemBlock) (k : Int) (v : LVec) : (m.write k v).shape = m.shape := by
  unfold MemBlock.write
  split <;> rfl

/-- **A block's read after a write**: the converted value at the written in-range label, the old read elsewhere. -/
theorem MemBlock.read_write (m : MemBlock) (k j : Int) (v : LVec) :
    (m.write k v).read j = if m.shape.inRange k ∧ j = k then m.shape.convert v else m.read j := by
  unfold MemBlock.write
  by_cases hk : m.shape.inRange k
  · simp only [hk, ↓reduceIte, true_and]
    by_cases hj : j = k
    · subst hj; simp [MemBlock.read, hk]
    · have hjk : (k == j) = false := by simpa using Ne.symm hj
      simp [MemBlock.read, hj, List.find?_cons, hjk]
  · simp [hk]

/-- A 4-state element conversion of a value of the element width changes nothing. -/
theorem MemShape.convert_of_width {m : MemShape} (h2 : m.twoState = false) {v : LVec} (hw : v.width = m.elemWidth) :
    m.convert v = v := by
  simp [MemShape.convert, h2, LVec.resizeU_of_width hw]

/-- **THE MEMORY COMMIT**: on a coherent memory state, the route's commit of the records of a view-level queue
(`MemState.commitNba`, in issue order) succeeds, stays coherent, and its memory view is `commitMemV` of the queue: one
write equation per record, never a cell expansion. -/
theorem CoreMemDesign.commitNba_V {E : CoreMemDesign} (hmo : E.memOkB = true) :
    ∀ (q : MemQV) (m : MemState), E.MemCoherent m → (∀ r ∈ q, E.RecOk r) →
      ∃ m', m.commitNba (q.map E.memRec) = some m' ∧ E.MemCoherent m' ∧ E.memOf m' = commitMemV (E.memOf m) q
  | [], m, hmc, _ => ⟨m, rfl, hmc, rfl⟩
  | (n, k, x) :: rest, m, hmc, hq => by
      obtain ⟨md, hmd, hin, hxw⟩ := hq (n, k, x) (by simp)
      obtain ⟨hmem, hname⟩ := CoreMemDesign.memDecl?_some hmd
      obtain ⟨-, hidn, hfour⟩ := CoreMemDesign.memOkB_spec hmo
      obtain ⟨blk, hb, hbe, hs, hw⟩ := hmc.blocks md hmem
      have hrec : E.memRec (n, k, x) = { id := md.shape.id, label := k, value := x } := by
        simp [CoreMemDesign.memRec, hmd]
      have hconv : blk.shape.convert x = x := by
        rw [hs]; exact MemShape.convert_of_width (hfour md hmem).2.2 hxw
      have hinb : blk.shape.inRange k := by rw [hs]; exact hin
      have hw1 : m.writeId md.shape.id k x = some (m.setId md.shape.id (blk.write k x)) := by
        simp [MemState.writeId, hb]
      have hc1 : E.MemCoherent (m.setId md.shape.id (blk.write k x)) := ⟨fun md' hmd' => by
        by_cases hid : md'.shape.id = md.shape.id
        · obtain rfl := eq_of_mem_map_nodup hidn hmd' hmem hid
          refine ⟨blk.write k x, by simp [MemState.setId_lookupId], by simp [MemState.setId_find],
            by rw [MemBlock.write_shape, hs], fun j => ?_⟩
          rw [MemBlock.read_write]
          split
          · rw [hs]; exact MemShape.width_convert _ _
          · exact hw j
        · obtain ⟨blk', hb', hbe', hs', hw'⟩ := hmc.blocks md' hmd'
          exact ⟨blk', by rw [MemState.setId_lookupId, if_neg hid]; exact hbe',
            by rw [MemState.setId_find, if_neg hid]; exact hbe', hs', hw'⟩⟩
      have hv1 : E.memOf (m.setId md.shape.id (blk.write k x)) = memWrite (E.memOf m) n (some k) x := by
        funext n' j
        simp only [CoreMemDesign.memOf, memWrite]
        cases hmd' : E.memDecl? n' with
        | none =>
            have hne : ¬ n' = n := fun h => by rw [h, hmd] at hmd'; exact absurd hmd' (by simp)
            simp [hne]
        | some md'' =>
            obtain ⟨hmem'', hname''⟩ := CoreMemDesign.memDecl?_some hmd'
            by_cases hid : md''.shape.id = md.shape.id
            · obtain rfl := eq_of_mem_map_nodup hidn hmem'' hmem hid
              have hn : n' = n := hname''.symm.trans hname
              subst hn
              simp only [MemState.setId_lookupId, ↓reduceIte, Option.map_some, Option.getD_some,
                MemBlock.read_write, hinb, true_and, hb, Option.some.injEq, hconv]
              by_cases hj : j = k
              · simp [hj]
              · simp [hj, Ne.symm hj]
            · have hne : ¬ n' = n := fun h => by
                rw [h, hmd] at hmd'; exact hid (by rw [Option.some.inj hmd'])
              obtain ⟨blk'', hb'', hbe'', -, -⟩ := hmc.blocks md'' hmem''
              simp [MemState.setId_lookupId, hid, hbe'', hb'', hne]
      obtain ⟨m', hm', hc', hv'⟩ := CoreMemDesign.commitNba_V hmo rest _ hc1 (fun r hr => hq r (by simp [hr]))
      refine ⟨m', ?_, hc', by rw [hv', hv1]; rfl⟩
      simp only [List.map_cons, hrec, MemState.commitNba_cons, hw1, Option.bind_some]
      exact hm'

#print axioms CoreMemDesign.commitNba_V

/-- No memory of the profile is an input port, so the route's `applyMemoryInputs` changes nothing. -/
theorem CoreMemDesign.applyMemoryInputs_id {E : CoreMemDesign} (hmo : E.memOkB = true) (entry : SvState)
    (m : MemState) : E.applyMemoryInputs entry m = m := by
  have hin : ∀ md ∈ E.memories.toList, md.source.isInput = false :=
    fun md hmd => ((CoreMemDesign.memOkB_spec hmo).2.2 md hmd).1
  unfold CoreMemDesign.applyMemoryInputs
  suffices h : ∀ (l : List CoreMemDecl) (m : MemState), (∀ md ∈ l, md.source.isInput = false) →
      l.foldl (fun mem md => if !md.source.isInput then mem else
        (List.range ((Int.natAbs (md.shape.msb - md.shape.lsb)) + 1)).foldl (fun m k =>
          let ki : Int := Int.ofNat k
          let i := if md.shape.lsb >= md.shape.msb then md.shape.msb + ki else md.shape.msb - ki
          match SvState.lookup entry (md.source.name ++ "[" ++ toString i ++ "]") with
          | none => m
          | some v => (m.writeId md.shape.id i (md.shape.convert v)).getD m) mem) m = m from h _ m hin
  intro l
  induction l with
  | nil => intro m _; rfl
  | cons md l ih =>
      intro m hl
      simp only [List.foldl_cons, hl md (by simp), Bool.not_false, ↓reduceIte]
      exact ih m (fun md' h => hl md' (by simp [h]))

theorem MemBlock.xBlock_read_width (s : MemShape) (k : Int) : ((MemBlock.xBlock s).read k).width = s.elemWidth := by
  unfold MemBlock.read
  split
  · simp only [MemBlock.xBlock, List.find?_nil, Option.map_none, Option.getD_none]
    exact (MemBlock.xBlock s).cell_width k
  · simp [LVec.xVec, LVec.replicate, LVec.width, MemBlock.xBlock]

/-- The route's x start of a memory list looks its blocks up in its entry table. -/
theorem MemState.ofShapes_lookupId (shapes : List MemShape) (id : MemId) :
    (MemState.ofShapes shapes).lookupId id = (((MemState.ofShapes shapes).entries.find? fun p => p.1 == id).map (·.2)) := by
  cases shapes <;> rfl

/-- The route's x start of a memory list (`MemState.ofShapes`, distinct identities) holds every block under its
identity. -/
theorem MemState.ofShapes_find : ∀ (shapes : List MemShape), (shapes.map fun s => s.id).Nodup → ∀ s ∈ shapes,
    (((MemState.ofShapes shapes).entries.find? fun p => p.1 == s.id).map (·.2)) = some (MemBlock.xBlock s)
  | [], _, s, hs => by simp at hs
  | t :: rest, hnd, s, hs => by
      simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
      have he : (MemState.ofShapes (t :: rest)).entries =
          (t.id, MemBlock.xBlock t) :: (MemState.ofShapes rest).entries.filter fun p => p.1 != t.id := rfl
      rw [he]
      simp only [List.mem_cons] at hs
      rcases hs with rfl | hs
      · simp [List.find?_cons]
      · have hne : s.id ≠ t.id := fun h => hnd.1 s hs h
        have hne' : (t.id == s.id) = false := by simpa using Ne.symm hne
        simp only [List.find?_cons, hne', find_filter_ne hne]
        exact MemState.ofShapes_find rest hnd.2 s hs

/-- **The route's x start is memory-coherent**: every memory starts as its typed x/z block. -/
theorem CoreMemDesign.initial_memCoherent {E : CoreMemDesign} (hmo : E.memOkB = true) :
    E.MemCoherent E.initial.memory := by
  obtain ⟨-, hidn, -⟩ := CoreMemDesign.memOkB_spec hmo
  have hnd : ((E.memories.toList.map CoreMemDecl.shape).map fun s => s.id).Nodup := by
    simpa [List.map_map, Function.comp_def] using hidn
  refine ⟨fun md hmd => ?_⟩
  have h2 := MemState.ofShapes_find _ hnd md.shape (List.mem_map_of_mem hmd)
  exact ⟨MemBlock.xBlock md.shape, (MemState.ofShapes_lookupId _ _).trans h2, h2, rfl,
    MemBlock.xBlock_read_width md.shape⟩

/-! ## The edge pass and the slot -/

/-- **The edge pass on views** (`runEdges`): every edge process whose clock rose or whose asynchronous reset fell from
the slot's start view `before` to the pre-edge view `after` (`CoreMemEdge.fires`: §9.4.2's edge table, x/z rows
included) runs its body on the threaded view (the memory view is read, never written); the updates are concatenated in
process order. -/
def CoreMemDesign.edgesV (E : CoreMemDesign) (before after : SvState) (v : SvState) (mv : MemV) :
    List CoreMemProc → Res ExecV
  | [] => .ok (v, [], [])
  | .edge p :: rest =>
      if p.fires before after then do
        let a ← E.execV E.env v mv p.body
        let b ← E.edgesV before after a.1 mv rest
        .ok (b.1, a.2.1 ++ b.2.1, a.2.2 ++ b.2.2)
      else E.edgesV before after v mv rest
  | .event evs body :: rest =>
      match coreMemEventEdge? evs body with
      | some p =>
          if p.fires before after then do
            let a ← E.execV E.env v mv p.body
            let b ← E.edgesV before after a.1 mv rest
            .ok (b.1, a.2.1 ++ b.2.1, a.2.2 ++ b.2.2)
          else E.edgesV before after v mv rest
      | none => E.edgesV before after v mv rest
  | _ :: rest => E.edgesV before after v mv rest

/-- The edge pass on views reads a plain `always` on one clock edge as its edge process. -/
theorem CoreMemDesign.edgesV_event {E : CoreMemDesign} {before after v : SvState} {mv : MemV}
    {evs : List CoreMemEvent} {body : PStmt} {f : CoreMemEdge} (h : coreMemEventEdge? evs body = some f)
    (rest : List CoreMemProc) :
    E.edgesV before after v mv (.event evs body :: rest) = E.edgesV before after v mv (.edge f :: rest) := by
  simp only [CoreMemDesign.edgesV, h]

/-- The edge pass on views skips an event process that is no edge process. -/
theorem CoreMemDesign.edgesV_event_none {E : CoreMemDesign} {before after v : SvState} {mv : MemV}
    {evs : List CoreMemEvent} {body : PStmt} (h : coreMemEventEdge? evs body = none) (rest : List CoreMemProc) :
    E.edgesV before after v mv (.event evs body :: rest) = E.edgesV before after v mv rest := by
  simp only [CoreMemDesign.edgesV, h]

/-- The edge pass on views at a process that is an edge process (`CoreMemProc.edge?`). -/
theorem CoreMemDesign.edgesV_cons_some {E : CoreMemDesign} {before after v : SvState} {mv : MemV} {p : CoreMemProc}
    {f : CoreMemEdge} (h : p.edge? = some f) (rest : List CoreMemProc) :
    E.edgesV before after v mv (p :: rest) =
      if f.fires before after then do
        let a ← E.execV E.env v mv f.body
        let b ← E.edgesV before after a.1 mv rest
        .ok (b.1, a.2.1 ++ b.2.1, a.2.2 ++ b.2.2)
      else E.edgesV before after v mv rest := by
  cases p with
  | edge g =>
      simp only [CoreMemProc.edge?, Option.some.injEq] at h
      subst h
      simp only [CoreMemDesign.edgesV]
  | event evs body =>
      simp only [CoreMemProc.edge?] at h
      simp only [CoreMemDesign.edgesV, h]
  | _ => exact absurd h (by simp [CoreMemProc.edge?])

/-- The edge pass on views skips a process that is no edge process. -/
theorem CoreMemDesign.edgesV_cons_none {E : CoreMemDesign} {before after v : SvState} {mv : MemV} {p : CoreMemProc}
    (h : p.edge? = none) (rest : List CoreMemProc) :
    E.edgesV before after v mv (p :: rest) = E.edgesV before after v mv rest := by
  cases p with
  | edge g => exact absurd h (by simp [CoreMemProc.edge?])
  | event evs body =>
      simp only [CoreMemProc.edge?] at h
      simp only [CoreMemDesign.edgesV, h]
  | _ => simp only [CoreMemDesign.edgesV]

/-- The shape of a process of the clocked profile, without its index (any clock, either edge). -/
def CoreMemDesign.ProcShapeI (E : CoreMemDesign) : CoreMemProc → Prop
  | .assign _ _ => True
  | .edge f => f.body.edgeOkB = true
  | .event evs body =>
      match coreMemEventEdge? evs body with
      | some f => f.body.edgeOkB = true
      | none => False
  | _ => False

theorem CoreMemDesign.ProcOkI.shape {E : CoreMemDesign} {i : Nat} {p : CoreMemProc}
    (h : E.ProcOkI i p) : E.ProcShapeI p := by
  cases p with
  | assign t v => trivial
  | edge f => exact h
  | primitive _ _ _ => exact absurd h (by simp [CoreMemDesign.ProcOkI])
  | initial _ => exact absurd h (by simp [CoreMemDesign.ProcOkI])
  | comb _ => exact absurd h (by simp [CoreMemDesign.ProcOkI])
  | implicit _ => exact absurd h (by simp [CoreMemDesign.ProcOkI])
  | event evs body => exact h
  | latch _ => exact absurd h (by simp [CoreMemDesign.ProcOkI])
  | unsupported _ _ => exact absurd h (by simp [CoreMemDesign.ProcOkI])

theorem CoreMemDesign.SeqProfileI.shapes {E : CoreMemDesign} (hP : E.SeqProfileI) :
    ∀ p ∈ E.processes.toList, E.ProcShapeI p := by
  intro p hp
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
  rw [Array.getElem?_toList] at hi
  exact (hP.procs i p hi).shape

theorem CoreMemDesign.SeqProfileI.hasComb {E : CoreMemDesign} (hP : E.SeqProfileI) :
    E.hasComb = false := by
  simp only [CoreMemDesign.hasComb, List.any_eq_false]
  intro p hp
  have := hP.shapes p hp
  cases p <;> simp_all [CoreMemDesign.ProcShapeI]

theorem CoreMemDesign.SeqProfileI.hasImplicit {E : CoreMemDesign} (hP : E.SeqProfileI) :
    E.hasImplicit = false := by
  simp only [CoreMemDesign.hasImplicit, List.any_eq_false]
  intro p hp
  have := hP.shapes p hp
  cases p <;> simp_all [CoreMemDesign.ProcShapeI]

/-- **The edge pass refinement**: from a coherent state with a coherent memory, when the view-level edge pass gives
`(v', q, mq)` the route's `runEdges` leaves a coherent state whose view is `v'`, with its memory unchanged, and issues
exactly `q` and the route's records of `mq`. -/
theorem CoreMemDesign.runEdges_V {E : CoreMemDesign}
    (hnd : (E.scalar.decls.toList.map Decl.name).Nodup) (h4 : AllFour E.scalar)
    (before after : SvState) :
    ∀ (procs : List CoreMemProc), (∀ p ∈ procs, E.ProcShapeI p) →
    ∀ (st : CoreMemState) (v' : SvState) (q : NbaQueue2) (mq : MemQV), E.Coherent st → E.MemCoherent st.memory →
      E.edgesV before after (E.scalar.view st.scalar) (E.memOf st.memory) procs = .ok (v', q, mq) →
      ∃ st', E.runEdges E.env E.elems st before after procs = .ok ⟨st', q, mq.map E.memRec, []⟩ ∧
        E.scalar.view st'.scalar = v' ∧ E.Coherent st' ∧ st'.memory = st.memory ∧ ∀ r ∈ mq, E.RecOk r
  | [], _, st, v', q, mq, hc, _, hv => by
      simp only [CoreMemDesign.edgesV, Res.ok.injEq, Prod.mk.injEq] at hv
      obtain ⟨rfl, rfl, rfl⟩ := hv
      exact ⟨st, rfl, rfl, hc, rfl, by simp⟩
  | p :: rest, h, st, v', q, mq, hc, hmc, hv => by
      have hrest : ∀ q ∈ rest, E.ProcShapeI q := fun q hq => h q (by simp [hq])
      have hp := h p (by simp)
      cases p with
      | edge f =>
          have hb := hp
          simp only [CoreMemDesign.edgesV] at hv
          by_cases hf : f.fires before after = true
          · simp only [hf, ↓reduceIte, Res.bind_eq_ok, Res.ok.injEq] at hv
            obtain ⟨⟨v1, a, ma⟩, h1, ⟨v2, b, mb⟩, h2, hq⟩ := hv
            simp only [Prod.mk.injEq] at hq
            obtain ⟨rfl, rfl, rfl⟩ := hq
            obtain ⟨st1, hs1, hv1, hc1, hm1, hr1⟩ :=
              CoreMemDesign.execStmtFuel_V hnd h4 f.body E.env
                (4096 + PStmt.need E.env f.body + PStmt.runtimeNeed E.env f.body)
                st v1 a ma hc hmc hb (by omega) h1
            obtain ⟨st2, hs2, hv2, hc2, hm2, hr2⟩ := CoreMemDesign.runEdges_V hnd h4 before after rest hrest st1
              v2 b mb hc1 (by rw [hm1]; exact hmc) (by rw [hv1, hm1]; exact h2)
            refine ⟨st2, by simp [CoreMemDesign.runEdges, hf, CoreMemDesign.execStmt, hs1, hs2, CoreMemExec.append],
              hv2, hc2, by rw [hm2, hm1], fun r hr => ?_⟩
            rcases List.mem_append.mp hr with hr | hr
            · exact hr1 r hr
            · exact hr2 r hr
          · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hv
            obtain ⟨st2, hs2, hv2, hc2, hm2, hr2⟩ :=
              CoreMemDesign.runEdges_V hnd h4 before after rest hrest st v' q mq hc hmc hv
            exact ⟨st2, by simp [CoreMemDesign.runEdges, hf, hs2], hv2, hc2, hm2, hr2⟩
      | assign t v =>
          simp only [CoreMemDesign.edgesV] at hv
          obtain ⟨st2, hs2, hv2, hc2, hm2, hr2⟩ :=
            CoreMemDesign.runEdges_V hnd h4 before after rest hrest st v' q mq hc hmc hv
          exact ⟨st2, by simp [CoreMemDesign.runEdges, hs2], hv2, hc2, hm2, hr2⟩
      | primitive _ _ _ => exact absurd hp (by simp [CoreMemDesign.ProcShapeI])
      | initial _ => exact absurd hp (by simp [CoreMemDesign.ProcShapeI])
      | comb _ => exact absurd hp (by simp [CoreMemDesign.ProcShapeI])
      | implicit _ => exact absurd hp (by simp [CoreMemDesign.ProcShapeI])
      | event evs body =>
          cases hfe : coreMemEventEdge? evs body with
          | none => exact absurd hp (by simp [CoreMemDesign.ProcShapeI, hfe])
          | some f =>
              simp only [CoreMemDesign.ProcShapeI, hfe] at hp
              rw [CoreMemDesign.edgesV_event hfe] at hv
              rw [CoreMemDesign.runEdges_event hfe]
              have hb := hp
              simp only [CoreMemDesign.edgesV] at hv
              by_cases hf : f.fires before after = true
              · simp only [hf, ↓reduceIte, Res.bind_eq_ok, Res.ok.injEq] at hv
                obtain ⟨⟨v1, a, ma⟩, h1, ⟨v2, b, mb⟩, h2, hq⟩ := hv
                simp only [Prod.mk.injEq] at hq
                obtain ⟨rfl, rfl, rfl⟩ := hq
                obtain ⟨st1, hs1, hv1, hc1, hm1, hr1⟩ :=
                  CoreMemDesign.execStmtFuel_V hnd h4 f.body E.env
                    (4096 + PStmt.need E.env f.body + PStmt.runtimeNeed E.env f.body)
                    st v1 a ma hc hmc hb (by omega) h1
                obtain ⟨st2, hs2, hv2, hc2, hm2, hr2⟩ := CoreMemDesign.runEdges_V hnd h4 before after rest hrest st1
                  v2 b mb hc1 (by rw [hm1]; exact hmc) (by rw [hv1, hm1]; exact h2)
                refine ⟨st2, by simp [CoreMemDesign.runEdges, hf, CoreMemDesign.execStmt, hs1, hs2, CoreMemExec.append],
                  hv2, hc2, by rw [hm2, hm1], fun r hr => ?_⟩
                rcases List.mem_append.mp hr with hr | hr
                · exact hr1 r hr
                · exact hr2 r hr
              · simp only [hf, Bool.false_eq_true, ↓reduceIte] at hv
                obtain ⟨st2, hs2, hv2, hc2, hm2, hr2⟩ :=
                  CoreMemDesign.runEdges_V hnd h4 before after rest hrest st v' q mq hc hmc hv
                exact ⟨st2, by simp [CoreMemDesign.runEdges, hf, hs2], hv2, hc2, hm2, hr2⟩
      | latch _ => exact absurd hp (by simp [CoreMemDesign.ProcShapeI])
      | unsupported _ _ => exact absurd hp (by simp [CoreMemDesign.ProcShapeI])

/-- **One slot of the route, on views**: the inputs applied, two settle passes (the pre-edge view), the edge pass from
the slot's start view to the pre-edge view, the commit of its updates (scalar updates on the view it leaves, memory
records on the memory view), two settle passes on the committed memory. -/
def CoreMemDesign.slotV (E : CoreMemDesign) (v : SvState) (mv : MemV) (entry : SvState) : Res (SvState × MemV) := do
  let p0 ← E.settleV mv (applyInputs2 E.scalar.toDesign2 entry v)
  let p ← E.settleV mv p0
  let r ← E.edgesV v p p mv E.processes.toList
  let s1 ← E.settleV (commitMemV mv r.2.2) (commitNba2 r.1 r.2.1)
  let s2 ← E.settleV (commitMemV mv r.2.2) s1
  .ok (s2, commitMemV mv r.2.2)

/-- Coherence does not read the memory. -/
theorem CoreMemDesign.Coherent.with_memory {E : CoreMemDesign} {st : CoreMemState} (hc : E.Coherent st)
    (m : MemState) : E.Coherent { st with memory := m } :=
  ⟨hc.store, hc.size, hc.typed⟩

/-! ## Instants, the input discipline, and the instant function

A run of the route is a list of rows (slot entries: new values for some inputs). The input discipline `Separated`
classifies each row from the inputs applied before it:
* a DATA ROW: no event of the design occurs (data inputs move, and event sources in a direction no process watches:
  the clock's return to 0 for a rising-edge design, an active-low reset's release);
* an INSTANT ROW: some event occurs, nothing but event sources moves, and no process sees its clock event while its
  asynchronous reset moves (`ResetStill`).
It is the general form of the clocking discipline "data while the clock is low, then the clock alone". Under it the
route's row resolution ("all inputs first") is the standard's only one: no process wakes in a data row; in an instant
row no data moves, a process woken by its clock reads no moving signal (`oblNoSourceRead`), and a process woken by its
reset reads the reset that woke it (§4.7: in one slot the stimulus may be suspended between two updates, so a process
woken by one update could otherwise read the other's old value). An asynchronous reset is an event like a clock edge:
its assertion is an instant (never with a data change), its release may share a data row.

An INSTANT is written as the levels its moving sources go to (`Instant.rise c` is `{posedge c}` from a low `c`); the
instant function `tick` is the mirror's slot on the instant's row, derived, never written by hand. A data row's view is
`dataV`. The cycle of the single-clock view is a data row then `tick (Instant.rise clk)`, by definition (`cycleMV`). -/

/-- **An instant**: the event sources that move in one slot, each with the level its least significant bit moves to.
The events it carries are the design's events those moves make from the levels before it (§9.4.2): `Instant.rise c` is
`{posedge c}` from a low (0, x or z) `c`, `[(a, .l1), (b, .l0)]` is `{posedge a, negedge b}` from `a` low and `b` high;
an edge into x or z is a move to `.lx` or `.lz`. -/
abbrev Instant := List (String × Logic)

/-- The row an instant makes: each moving source at its new level. -/
def Instant.row (i : Instant) : SvState := i.map fun m => (m.1, ⟨#[m.2]⟩)

/-- `{posedge c}` (from a low `c`). -/
def Instant.rise (c : String) : Instant := [(c, .l1)]

/-- `{negedge c}` (from a high `c`). -/
def Instant.fall (c : String) : Instant := [(c, .l0)]

/-- The single-clock high slot is the instant `{posedge clk}`. -/
theorem Instant.rise_row (c : String) : (Instant.rise c).row = highEntry c := rfl

/-- The inputs a row applies to the view before it (nothing settles: the inputs a run has applied so far). -/
def CoreMemDesign.applyRow (E : CoreMemDesign) (v r : SvState) : SvState := applyInputs2 E.scalar.toDesign2 r v

/-- No process sees its clock event while its asynchronous reset moves (the process reads its reset as data; with both
in one slot the standard lets it run on either value, §4.7). -/
def CoreMemDesign.ResetStill (E : CoreMemDesign) (v w : SvState) : Prop :=
  ∀ f, f ∈ E.edgeProcs → f.clockEvent.occursIn v w = true →
    ∀ r, f.reset = some r → SvState.lookup w r = SvState.lookup v r

/-- **A data row** from the view `v`: no event of the design occurs. -/
def CoreMemDesign.DataRow (E : CoreMemDesign) (v r : SvState) : Prop := E.occurs v (E.applyRow v r) = []

/-- **An instant row** from the view `v`: some event of the design occurs, nothing but event sources moves, and no
process sees its clock event while its reset moves. -/
def CoreMemDesign.InstantRow (E : CoreMemDesign) (v r : SvState) : Prop :=
  E.occurs v (E.applyRow v r) ≠ [] ∧
    (∀ n, n ∉ E.sources → SvState.lookup (E.applyRow v r) n = SvState.lookup v n) ∧ E.ResetStill v (E.applyRow v r)

/-- **THE INPUT DISCIPLINE**: every row is a data row or an instant row, read from the inputs applied before it (a
property of the stimulus and the start state's inputs only). -/
def CoreMemDesign.Separated (E : CoreMemDesign) : SvState → List SvState → Prop
  | _, [] => True
  | v, r :: rs => (E.DataRow v r ∨ E.InstantRow v r) ∧ E.Separated (E.applyRow v r) rs

/-- **The instant an instant row makes** from `v`: the event sources it moves, with their new levels. -/
def CoreMemDesign.instOf (E : CoreMemDesign) (v r : SvState) : Instant :=
  E.sources.eraseDups.filterMap fun s =>
    if SvState.lookup (E.applyRow v r) s = SvState.lookup v s then none else some (s, (E.applyRow v r).bit0 s)

/-- **A data row on views**: the mirror's slot on the row. -/
def CoreMemDesign.dataV (E : CoreMemDesign) (σ : SvState × MemV) (d : SvState) : Res (SvState × MemV) :=
  E.slotV σ.1 σ.2 d

/-- **THE INSTANT FUNCTION**, derived from the design through the mirror: the slot on the instant's row (the processes
whose events the instant carries run on the pre-edge view, their updates commit, the region settles). -/
def CoreMemDesign.tick (E : CoreMemDesign) (i : Instant) (σ : SvState × MemV) : Res (SvState × MemV) :=
  E.slotV σ.1 σ.2 i.row

/-! ## The cycle: the single-clock view, a data row then the instant `{posedge clk}` -/

/-- **One clock cycle on views**, the one-event instance of the instant view: the low slot (a data row: the cycle's
data and `clk` at 0), then the instant `{posedge clk}`; the pre sample and the post sample, each a view and a memory
view. -/
def CoreMemDesign.cycleMV (E : CoreMemDesign) (clk : String) (σ : SvState × MemV) (data : SvState) :
    Res ((SvState × MemV) × (SvState × MemV)) := do
  let pre ← E.dataV σ (lowEntry clk data)
  let post ← E.tick (Instant.rise clk) pre
  .ok (pre, post)

/-- The cycle is the mirror's two slots (the form the evaluation pass computes). -/
theorem CoreMemDesign.cycleMV_slots (E : CoreMemDesign) (clk : String) (σ : SvState × MemV) (data : SvState) :
    E.cycleMV clk σ data = (do
      let pre ← E.slotV σ.1 σ.2 (lowEntry clk data)
      let post ← E.slotV pre.1 pre.2 (highEntry clk)
      .ok (pre, post)) := rfl

/-- **One clock cycle of a design without memories**: the scalar part of `cycleMV` (the memory view is never read). -/
def CoreMemDesign.cycleV (E : CoreMemDesign) (clk : String) (v data : SvState) : Res (SvState × SvState) := do
  let r ← E.cycleMV clk (v, memNone) data
  .ok (r.1.1, r.2.1)

/-! ## The x start and typed entries -/

/-- The x start of the route (`CoreMemDesign.initial`: every variable x, every net z) is coherent. -/
theorem CoreMemDesign.initial_coherent (E : CoreMemDesign) : E.Coherent E.initial :=
  { store := rfl
    size := by simp [CoreMemDesign.initial, CoreMemDesign.scalarCacheOf]
    typed := Elab.typed_congr_decls (fun j hj => (E.scalarStore_cacheOf _ j hj).symm) E.scalar.typed_initStore }

/-- A data entry of a cycle is typed: every input port it binds gets a value of its declared width. -/
def CoreMemDesign.DataTyped (E : CoreMemDesign) (clk : String) (d : SvState) : Prop :=
  EntryTyped E.scalar.toDesign2 (lowEntry clk d)

theorem CoreMemDesign.highEntry_typed {E : CoreMemDesign} {clk : String}
    (hclk : E.scalar.toDesign2.declWidth clk = some 1) : EntryTyped E.scalar.toDesign2 (highEntry clk) := by
  intro n v _ hv
  simp only [highEntry] at hv
  unfold SvState.lookup at hv
  split at hv
  · rename_i h
    simp only [Option.some.injEq] at hv
    subst hv
    have : clk = n := by simpa using h
    subst this
    exact hclk
  · simp [SvState.lookup] at hv

theorem CoreMemDesign.DataTyped.of_entry {E : CoreMemDesign} {clk : String}
    (hclk : E.scalar.toDesign2.declWidth clk = some 1) {d : SvState} (hd : EntryTyped E.scalar.toDesign2 d) :
    E.DataTyped clk d := by
  intro n v hn hv
  simp only [lowEntry, SvState.lookup] at hv
  split at hv
  · rename_i h
    simp only [Option.some.injEq] at hv
    subst hv
    have : clk = n := by simpa using h
    subst this
    exact hclk
  · exact hd n v hn hv

end LeanModels.Sv.Kernel
