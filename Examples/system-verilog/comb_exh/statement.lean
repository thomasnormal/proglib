import LeanModels.Sv.CombTask
import LeanModels.Sv.Comb2Proc

/-!
# The svGolf task vocabulary that `sv_exhaustive` closes, restated over ls-sv (comb_exh)

`sv_exhaustive` (`LeanModels/Sv/CombExhaustiveTactic.lean`) proves a fixed-size combinational task statement of svGolf
(`svgolf/SvGolf/Task.lean`: `CombTask.StatementFixed`, its three conjuncts `Interface`, `Unclocked ∧ LoopFree ∧
Terminates2` and `Computes`) through svGolf's reductions (`svgolf/SvGolf/Comb.lean`: `CombTask.satisfiedAt_of_comb`,
`CombTask.satisfiedAt_of_lowered`, the simp lemmas `HoldAll_cons`/`HoldAll_nil`), which it names `SvGolf.…` and which
are resolved in the user's file. `LeanModels` may not import `svgolf`, so this file restates that vocabulary over
ls-sv alone, in a namespace `SvGolf` nested in this module's namespace (`open` it and the tactic's names resolve): the
definitions are svGolf's, with the ports read by `Design2.inputPorts`/`Design2.outputPorts` (`CombTask.lean`, svGolf's
`inputPorts`/`outputPorts` verbatim), and the two reductions are proved here from the same ls-sv theorems svGolf's
proofs use. Nothing here is trusted beyond the definitions; every theorem is proved.

The tests (`exh_proof.lean`, `exh_errors.lean`) run `sv_exhaustive` to success on a table design and a gate design, and
pin its refusal of a wrong table: until this directory, nothing in this repository ran the tactic to success, and a
broken premise (the atom-free premise of `Summary.autoObl_of_plain`) stayed unnoticed for four rounds.
-/

namespace Examples.«system-verilog».comb_exh.statement

open LeanModels.Sv

namespace SvGolf

/-- A port signature: the port's name and its width in bits. -/
abbrev Sig := String × Nat

/-- One known value per port: `Vals [w₁, …, wₖ] = BitVec w₁ × (… × (BitVec wₖ × Unit))`. -/
@[reducible] def Vals : List Nat → Type
  | [] => Unit
  | w :: ws => BitVec w × Vals ws

/-- `HoldAll st sigs v`: in state `st`, every port `(n, w)` of `sigs` is bound to the fully known `w`-bit vector that
`v` assigns it. -/
def HoldAll (st : SvState) : (sigs : List Sig) → Vals (sigs.map Prod.snd) → Prop
  | [], _ => True
  | (n, _) :: sigs, v => SvState.lookup st n = some (LVec.ofBitVec v.1) ∧ HoldAll st sigs v.2

/-- No process of `d` is clocked. -/
def Unclocked (d : Design2) : Prop :=
  ∀ p ∈ d.processes.toList, p.isEdgePhase = false

/-- No combinational loop: `d` lowers to continuous assigns and the lowering is acyclic. -/
def LoopFree (d : Design2) : Prop :=
  ∃ d', d.lowerComb = some d' ∧ Acyclic d'

/-- A combinational task for a one-parameter design family. -/
structure CombTask where
  inRange : Nat → Prop
  inputs : Nat → List Sig
  outputs : Nat → List Sig
  fn : (N : Nat) → Vals ((inputs N).map Prod.snd) → Vals ((outputs N).map Prod.snd)

namespace CombTask

variable (t : CombTask)

/-- Conjunct 1: the design's input and output ports are exactly the task's. -/
def Interface (N : Nat) (d : Design2) : Prop :=
  d.inputPorts = t.inputs N ∧ d.outputPorts = t.outputs N

/-- Conjunct 3: every cycle whose stimulus drives each input port with a known value ends in a snapshot whose output
ports hold `t.fn N` of those values. -/
def Computes (N : Nat) (d : Design2) : Prop :=
  d ⊨₂ spec2 fun stim tr =>
    ∀ (c : Nat) (inputs st : SvState), stim[c]? = some inputs → tr[c]? = some st →
      ∀ v, HoldAll inputs (t.inputs N) v → HoldAll st (t.outputs N) (t.fn N v)

/-- The statement at one parameter value. -/
def SatisfiedAt (N : Nat) (d : Design2) : Prop :=
  t.Interface N d ∧ (Unclocked d ∧ LoopFree d ∧ Terminates2 d) ∧ t.Computes N d

/-- The statement for a parameterless design: the task at parameter value `0`. -/
def StatementFixed (d : Design2) : Prop :=
  t.SatisfiedAt 0 d

end CombTask

@[simp] theorem HoldAll_nil (st : SvState) (v : Vals (([] : List Sig).map Prod.snd)) :
    HoldAll st [] v ↔ True := Iff.rfl

@[simp] theorem HoldAll_cons (st : SvState) (n : String) (w : Nat) (sigs : List Sig)
    (v : Vals (((n, w) :: sigs).map Prod.snd)) :
    HoldAll st ((n, w) :: sigs) v ↔
      SvState.lookup st n = some (LVec.ofBitVec v.1) ∧ HoldAll st sigs v.2 := Iff.rfl

/-- `HoldAll` moves along any state that agrees on the ports' bindings. -/
theorem HoldAll.transfer {a b : SvState} :
    ∀ {sigs : List Sig} {v : Vals (sigs.map Prod.snd)}, HoldAll a sigs v →
      (∀ n ∈ sigs.map Prod.fst, ∀ val, SvState.lookup a n = some val → SvState.lookup b n = some val) →
      HoldAll b sigs v
  | [], _, _, _ => trivial
  | (n, _) :: _, _, ⟨h1, h2⟩, h =>
      ⟨h n (by simp) _ h1, HoldAll.transfer h2 fun m hm => h m (by simp [hm])⟩

/-- svGolf's comb reduction (`svgolf/SvGolf/Comb.lean`), over ls-sv: the statement at one parameter value from the
interface, the comb profile, a rank certificate and one settled-state lemma. -/
theorem CombTask.satisfiedAt_of_comb {t : CombTask} {N : Nat} {d : Design2}
    (hI : t.Interface N d) (hd : CombDesign d) (ha : Acyclic d)
    (hset : ∀ st, CombEqs d st → StateShape d st → ∀ v, HoldAll st (t.inputs N) v →
      HoldAll st (t.outputs N) (t.fn N v)) :
    t.SatisfiedAt N d := by
  refine ⟨hI, ⟨hd.unclocked, ⟨d, hd.lowerComb_eq, ha⟩, Terminates2.of_acyclic hd ha⟩, ?_⟩
  apply Models2.of_comb_inputs hd
  intro stim tr h c inputs st hi hc v hv
  obtain ⟨heqs, hs, hin⟩ := h c st hc
  refine hset st heqs hs v (hv.transfer fun n hn val hval => hin inputs hi n ?_ val hval)
  rw [← Design2.inputPorts_map_fst, hI.1]
  exact hn

/-- svGolf's reduction for a design that lowers to a comb design (`svgolf/SvGolf/Comb.lean`), over ls-sv. -/
theorem CombTask.satisfiedAt_of_lowered {t : CombTask} {N : Nat} {d d' : Design2}
    (hI : t.Interface N d) (hl : d.lowerComb = some d') (hd : CombDesign d') (ha : Acyclic d')
    (hnq : d.processes.toList.any Process2.hasQualifiedCase = false)
    (hset : ∀ st, CombEqs d' st → StateShape d' st → ∀ v, HoldAll st (t.inputs N) v →
      HoldAll st (t.outputs N) (t.fn N v)) :
    t.SatisfiedAt N d := by
  obtain ⟨hph, -, -⟩ := Design2.lowerComb_phases hl
  have hunc : Unclocked d := by
    intro p hp
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
    rw [Array.getElem?_toList] at hi
    have hlt : i < d.processes.size := by
      rcases Nat.lt_or_ge i d.processes.size with hlt | hge
      · exact hlt
      · rw [Array.getElem?_eq_none hge] at hi
        cases hi
    unfold Design2.edgeIndices at hph
    rw [List.filter_eq_nil_iff] at hph
    have := hph i (List.mem_range.mpr hlt)
    simpa [hi] using this
  refine ⟨hI, ⟨hunc, ⟨d', hl, ha⟩, Terminates2.of_lowerComb_acyclic hl hd ha hnq⟩, ?_⟩
  apply Models2.of_combProc_inputs hl hd (hnq := hnq)
  intro stim tr h c inputs st hi hc v hv
  obtain ⟨heqs, hs, hin⟩ := h c st hc
  refine hset st heqs hs v (hv.transfer fun n hn val hval => hin inputs hi n ?_ val hval)
  have hdec : d'.decls = d.decls := by
    unfold Design2.lowerComb at hl
    rcases hp : d.lowerProcs d.processes.toList with _ | ps
    · simp [hp] at hl
    · simp only [hp, Option.map_some, Option.some.injEq] at hl
      rw [← hl]
  rw [show d'.inputNames = d.inputNames by simp [Design2.inputNames, hdec], ← Design2.inputPorts_map_fst, hI.1]
  exact hn

end SvGolf

end Examples.«system-verilog».comb_exh.statement
