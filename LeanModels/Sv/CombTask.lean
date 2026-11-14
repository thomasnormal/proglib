import LeanModels.Sv.Comb2Proc

/-!
# Statement glue for combinational tasks (comb lane, proof plumbing)

A combinational task statement (svGolf's `CombTask.SatisfiedAt`, `svgolf/SvGolf/Task.lean`, is the model; `LeanModels`
may not import `svgolf`) asks of a design `d` for its ports, for no clocked process, for no combinational loop, for
termination, and for a function of the inputs in every cycle of every completed run. For a design in the comb profile
with a rank certificate (`CombDesign d`, `Acyclic d`: the products of `sv_structure`) everything but the ports and the
function is generic, and this file proves it once:

* `Design2.inputPorts`, `Design2.outputPorts`: the ports with their declared widths, in declaration order (svGolf's
  `inputPorts`/`outputPorts`); `sv_interface` proves them for a design the recognizer reads;
* `CombDesign.unclocked`: no process runs in the edge phase (every process is a continuous assign);
* `CombDesign.lowerComb_eq`: a comb-profile design lowers to itself, so `Acyclic d` is its loop-freedom;
* `Models2.of_comb_ports`: a property of every cycle's stimulus entry and snapshot, from the settled-state form, where
  each input port the entry drives holds the driven value;
* `CombTask.of_comb` (tac6): the whole statement shape (ports, the generic conjuncts, the stimulus form) from
  `CombDesign`, `Acyclic` and the ports, so a task proof starts at the settled-state goal.

Nothing here is trusted: every theorem is proved, and nothing mentions a tactic.
-/

namespace LeanModels.Sv

/-- The input ports of `d` with their declared widths, in declaration order (a declaration is an input port iff its
`isInput` flag is set). -/
def Design2.inputPorts (d : Design2) : List (String × Nat) :=
  d.decls.toList.filterMap fun dc => if dc.isInput then some (dc.name, dc.width) else none

/-- The output ports of `d` with their declared widths, in declaration order. -/
def Design2.outputPorts (d : Design2) : List (String × Nat) :=
  d.decls.toList.filterMap fun dc => if dc.isOutput then some (dc.name, dc.width) else none

/-- The input ports' names are the names `applyInputs2` reads (`Design2.inputNames`). -/
theorem Design2.inputPorts_map_fst (d : Design2) : d.inputPorts.map Prod.fst = d.inputNames.toList := by
  simp only [Design2.inputPorts, Design2.inputNames, Array.toList_filterMap]
  generalize d.decls.toList = l
  induction l with
  | nil => rfl
  | cons dc l ih => by_cases h : dc.isInput = true <;> simp [h, ih]

/-- A comb-profile design has no clocked process: each of its processes is a continuous assign. -/
theorem CombDesign.unclocked {d : Design2} (hd : CombDesign d) :
    ∀ p ∈ d.processes.toList, p.isEdgePhase = false := by
  intro p hp
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
  rw [Array.getElem?_toList] at hi
  obtain ⟨t, e, -, rfl, -⟩ := hd.assign i p hi
  rfl

/-- A list of continuous assigns lowers to itself. -/
theorem Design2.lowerProcs_of_assigns (d : Design2) :
    ∀ ps : List Process2, (∀ p ∈ ps, ∃ t e, p = .assign t e) → d.lowerProcs ps = some ps
  | [], _ => rfl
  | p :: ps, h => by
      obtain ⟨t, e, rfl⟩ := h p (by simp)
      have ih := Design2.lowerProcs_of_assigns d ps fun q hq => h q (by simp [hq])
      simp [Design2.lowerProcs, Process2.lowerComb, ih]

/-- A comb-profile design lowers to itself (`Design2.lowerComb`), so its own `Acyclic` certificate is the
loop-freedom of its lowering. -/
theorem CombDesign.lowerComb_eq {d : Design2} (hd : CombDesign d) : d.lowerComb = some d := by
  have hall : ∀ p ∈ d.processes.toList, ∃ t e, p = .assign t e := by
    intro p hp
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
    rw [Array.getElem?_toList] at hi
    obtain ⟨t, e, -, rfl, -⟩ := hd.assign i p hi
    exact ⟨t, e, rfl⟩
  unfold Design2.lowerComb
  rw [Design2.lowerProcs_of_assigns d _ hall]
  simp

/-- **The stimulus form of a property of every cycle**, for a comb-profile design: `Q inputs st` for the stimulus
entry `inputs` and the snapshot `st` of every cycle of every completed run follows from the settled-state form, in
which the snapshot solves the design's equations (`CombEqs`), has the comb shape (`StateShape`), and holds every value
the entry gives an input port of `d` (`Design2.inputPorts`). -/
theorem Models2.of_comb_ports {d : Design2} (hd : CombDesign d) {Q : SvState → SvState → Prop}
    (hQ : ∀ inputs st, CombEqs d st → StateShape d st →
      (∀ n ∈ d.inputPorts.map Prod.fst, ∀ v, SvState.lookup inputs n = some v → SvState.lookup st n = some v) →
      Q inputs st) :
    d ⊨₂ spec2 fun stim tr => ∀ (c : Nat) (inputs st : SvState),
      stim[c]? = some inputs → tr[c]? = some st → Q inputs st := by
  apply Models2.of_comb_inputs hd
  intro stim tr h c inputs st hi hc
  obtain ⟨heqs, hs, hin⟩ := h c st hc
  exact hQ inputs st heqs hs fun n hn v hv => hin inputs hi n (by rwa [Design2.inputPorts_map_fst] at hn) v hv

/-- **A combinational task's statement from the comb products** (tac6): the ports `ins`/`outs`, no clocked process, the
design its own lowering with the rank certificate `ha`, termination, and a property `Q` of every cycle's stimulus entry
and snapshot, from the settled-state form (`Models2.of_comb_ports`, with the port list read through `hp`). The shape is
the statement of a combinational task (svGolf's `CombTask.SatisfiedAt` unfolded, e.g. `prefix_ks/statement.lean`). -/
theorem CombTask.of_comb {d : Design2} {ins outs : List (String × Nat)} {Q : SvState → SvState → Prop}
    (hc : CombDesign d) (ha : Acyclic d) (hp : d.inputPorts = ins ∧ d.outputPorts = outs)
    (hQ : ∀ inputs st, CombEqs d st → StateShape d st →
      (∀ n ∈ ins.map Prod.fst, ∀ v, SvState.lookup inputs n = some v → SvState.lookup st n = some v) →
      Q inputs st) :
    (d.inputPorts = ins ∧ d.outputPorts = outs) ∧
      ((∀ p ∈ d.processes.toList, p.isEdgePhase = false) ∧ (∃ d', d.lowerComb = some d' ∧ Acyclic d') ∧
        Terminates2 d) ∧
      d ⊨₂ spec2 fun stim tr => ∀ (c : Nat) (inputs st : SvState),
        stim[c]? = some inputs → tr[c]? = some st → Q inputs st :=
  ⟨hp, ⟨hc.unclocked, ⟨_, hc.lowerComb_eq, ha⟩, Terminates2.of_acyclic hc ha⟩,
    Models2.of_comb_ports hc fun inputs st heqs hsh hin => hQ inputs st heqs hsh (by rw [← hp.1]; exact hin)⟩

/-- A one-bit vector is the `BitVec.ofBool` of its bit (the port of a task statement's `cin : BitVec 1`, read as the
`Bool` the equations hold). -/
theorem CombTask.bv1_eq_ofBool (x : BitVec 1) : x = BitVec.ofBool (x.getLsbD 0) :=
  BitVec.eq_of_getLsbD_eq fun i hi => by obtain rfl : i = 0 := (by omega); simp

end LeanModels.Sv
