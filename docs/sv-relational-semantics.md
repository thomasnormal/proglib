# Relational semantics for SystemVerilog

This note records the normative meaning of the SystemVerilog lane. The
meaning is a fuel-free relation that quantifies over every order allowed by
IEEE 1800-2023 and every 0/1 resolution of an x or z where the standard leaves
that resolution open. The function-based executor remains an implementation
used for differential runs and proof automation.

## Judgments and the current boundary

The first relational layer already in the tree is the source-shaped scheduler
in `LeanModels/Sv/Scheduler.lean`.

```lean
def oneStep (d : SchedulerDesign) (s t : SlotState) : Prop
def Slot (d : SchedulerDesign) (s t : SlotState) : Prop
def Run (d : SchedulerDesign) : List SvState → SlotState → List SvState → Prop
```

`oneStep` selects one legal active, NBA, or update event. `Slot` is its
reflexive-transitive closure ending in a quiet state. `Run` chains slots over
input rows. `SchedulerDesign` is the scheduler's source-shaped M0 view, so
these judgments are relational but are not yet the canonical-E relation.

`LeanModels/Sv/Kernel/CoreMemResume.lean` contains the corresponding
canonical-E phase relations.

```lean
inductive CombPhaseStep (E : CoreMemDesign) : CombPhaseState → CombPhaseState → Prop
inductive EdgePhaseStep (E : CoreMemDesign) : EdgePhaseState → EdgePhaseState → Prop
```

They retain parser-shaped cursors and permit any active cursor to be selected.
`EdgePhaseStep` also retains issue-time scalar and memory NBA queues. Its
`progress` theorem proves existence of a next step when all active cursors can
resume. The local diamond and the bridge from these relations to the complete
canonical slot are not proved for the memory class yet.

The following definitions are executable functions and therefore are not the
normative judgment.

```lean
CoreMemDesign.evalV
CoreMemDesign.execV
CoreMemDesign.edgesV
CoreMemDesign.slotV
CoreMemDesign.step
```

`execV` evaluates an admitted statement on a fixed view. `edgesV` evaluates
edge bodies in source order. `slotV` and `step` perform the canonical input,
settle, edge, NBA, and settle phases. Their results are in `Res`, and their
internal limits are implementation guards.

## Relation rules

The rules follow the parser node that they interpret. No rule lowers a node to
another construct before applying its meaning.

* An expression evaluates its operands in the order fixed by its construct.
  Four-state operators use the shared `LVec` tables. An x or z at a decision
  contributes every permitted 0/1 resolution to the relation. Arithmetic and
  conditional expression cases follow IEEE 1800-2023 §§11.4 and 11.4.11.
* A blocking assignment evaluates its RHS at the assignment event and updates
  the current state. A nonblocking assignment evaluates its RHS in the Active
  region and emits an update event for the NBA region, as required by
  §10.4.2.
* A block executes its parser-shaped statements in source order within that
  process. The scheduler may interleave distinct processes at every legal
  §4.7 preemption point.
* An `if` evaluates its condition and relates the result to the selected arm.
  A `case` evaluates its subject and relates it to each arm permitted by the
  case mode and four-state matching rules in §12.5.
* A `for` loop relates a state to the next loop state by the two rules in
  §12.7. A false condition relates directly to loop completion. A true
  condition relates through one body execution and then another loop judgment.
  Nontermination has no related result. The executor's `forValues2` list is an
  implementation of this rule for its admitted header profile.
* Continuous assignments and reactive processes are scheduled in the regions
  of §§4.4 and 4.5. A process is not sensitive to a signal while it is
  executing, as required by §9.4.2. NBA updates can enqueue later events in the
  same time slot.
* The scheduler relation permits every active-event order allowed by §§4.6,
  4.7, and 4.9.4. It preserves the NBA ordering rule in §10.4.2 and the
  source order within one process. A design that depends on an unproved order
  remains refused.
* A memory-element NBA carries its declaration identity, index resolution, and
  issue-time value into the NBA relation. The source-shaped memory-loop
  receipts in `LeanModels/Sv/SeqCycleObl.lean` are implementation facts that
  will be connected to this rule.

An unsupported parser node has no rule in the current relation. The loader and
executor refuse it loudly. A relation is not manufactured by assigning a
default value or by truncating a nonterminating derivation.

## Bridges and status

The current proof inventory has these levels.

* **Abstract lemma.** `ScheduleConfluence` in `Scheduler.lean` proves that a
  relation with a decreasing measure, progress, and a local diamond has one
  terminal state. It is independent of a concrete SystemVerilog design.
* **NBA rung.** `edgesV_order` proves scalar whole-signal NBA order
  independence under `seqOblI`. `edgesV_local_diamond` packages the two-choice
  consequence for the same route.
* **Frame lemmas.** `readsV_eq_instExpr2_idents_of_pure`,
  `evalExprLocals_congr_readsV_of_pure`, and the scalar write-order lemmas use
  the real `evalExprLocals` and `setScalarState`. They establish that parser
  read closure and evaluator reads agree in the pure fragment, and that
  disjoint coherent scalar writes commute.
* **Memory writes.** `edgesV_perm_memory` and `edgesV_order_memory` compare
  scalar and memory commits for arbitrary initial views while retaining an
  explicit evaluator frame receipt. `seqOblIM` and `step_seqIM` route the
  memory-aware obligation to the canonical step. The `memoryLeafB` and
  procedural-loop receipts now derive that frame for the narrow source-shaped
  profile. The broad parser predicate and the canonical relational diamond are
  still open.

The intended canonical bridge has the following shape. The names below are
proposed public relation names, not declarations that exist today.

```lean
def StepRel (E : CoreMemDesign) (s : CoreMemState) (i : SvState)
    (s' : CoreMemState) : Prop :=
  ∃ t, CanonicalSlotRel E s i t ∧ t.state = s'

def ExecStep (E : CoreMemDesign) (fuel : Nat) (s : CoreMemState) (i : SvState)
    (s' : CoreMemState) : Prop :=
  E.execFuel fuel s i = .ok s'

theorem exec_sound : ExecStep E fuel s i s' → StepRel E s i s'
theorem exec_complete_unique : DeterministicClass E →
    StepRel E s i s' → ∃ fuel, ExecStep E fuel s i s'
theorem step_unique : DeterministicClass E →
    StepRel E s i s₁ → StepRel E s i s₂ → s₁ = s₂
```

The cheap first bridge defines `StepExec` as the existential fuel wrapper
around the existing fuel-bearing implementation. A proved fuel-monotonicity
lemma makes this wrapper independent of the particular successful budget.
The soundness theorem is the first target. Completeness and uniqueness are
proved construct by construct where the language is deterministic. A refusal
or a diverging derivation has no related result.

## User-facing theorem statements

User theorems quantify over the relation and expose observable states. A run is
the reflexive-transitive closure of `StepRel`, or an infinite stream relation
when a property concerns an unbounded execution.

For a two-flop synchronizer, the intended statement is

```lean
theorem sync_two_flop_relational
    (hdesign : SyncAdmitted E) :
    ∀ s input s₁ s₂,
      StepRel E s input s₁ → StepRel E s input s₂ →
      observable E s₁ = observable E s₂ ∧
      syncInvariant s₁ ∧ syncInvariant s₂ := by
  ...
```

The hypotheses name the real admission conditions. The proof covers every
active-event order and every permitted input and x resolution.

For the memory FIFO reset loop, the intended statement is

```lean
theorem fifo_reset_loop_relational
    (hdesign : FifoMemoryAdmitted E) :
    ∀ s input s',
      coherent s →
      StepRel E s input s' →
      reset input →
      (∀ k, 0 ≤ k → k < depth → memoryView s' k = zero) ∧
      fifoInvariant s' := by
  ...
```

The loop is retained as a loop in the relation. The proof does not unroll a
parameterized depth. The memory edge-order work is the concrete content needed
to show that all legal process orders relate the same reset result.

## Migration order and failure modes

1. Keep `Scheduler.oneStep`, `Slot`, `Run`, `CombPhaseStep`, and
   `EdgePhaseStep` as the initial relation surfaces. Document their precise
   clause boundary and do not silently identify them with canonical E.
2. Add a fuel-parameterized public implementation wrapper and prove
   fuel-monotonicity. Prove `exec_sound` for expressions, statements, memory
   records, and the scheduler regions in parser-node order.
3. Connect the canonical E phase relations to `CoreMemDesign.execV` and
   `CoreMemDesign.step`. The scalar NBA rung and the memory-leaf loop receipts
   are the first concrete cases.
4. Prove local diamonds from the frame and admission lemmas. Then instantiate
   `ScheduleConfluence` for the admitted class and derive uniqueness of a
   terminal observable state.
5. Migrate example and user-facing theorems to `StepRel` or its run closure.
   Keep differential tests through the executable implementation and record
   the simulator trace as one related behaviour.
6. Widen memory cases, asynchronous events, continuous-assignment reactivity,
   multiple clocks, and x resolution only with their own rules and bridges.

The main failure modes are treating a source-order function as the meaning,
letting fuel appear in a user theorem, proving only one convenient schedule,
using a parser predicate as if it were an evaluator receipt, lowering a loop
into an untrusted list, or declaring confluence without proving its local
diamond from the guards. Each leaves a false theorem or hides a legal
behaviour. The relation must stay primary when the implementation and the
standard disagree.

## Proposed engineering-rule wording

Add the following line to the shared engineering rules.

> Define SystemVerilog's normative meaning as a fuel-free relation over
> parser-native nodes, scheduler regions, and all choices allowed by IEEE
> 1800. An executable function is an implementation and requires a
> kernel-checked soundness theorem to that relation. Fuel may occur only in
> implementation judgments and their bridges. User theorems quantify over
> every legal schedule, input, and x/z resolution, and unsupported or
> nonterminating constructs have no fabricated related result.

