# Relational semantics for SystemVerilog

This document is the v2 design requested by the owner ruling on
2026-11-24. The normative meaning is a fuel-free relation over the
parser-native, memory-capable SystemVerilog representation. The existing
function-based executor remains an implementation and a differential-test
instrument. No implementation of this relation starts until this design is
accepted.

The relation is built on the source-shaped nodes in `CoreMemDesign`,
`PStmt`, `PExpr`, and `PLhs`, and on the cursor and phase shape in
`LeanModels/Sv/Kernel/CoreMemResume.lean`. It does not make
`Scheduler.lean`'s older scalar `Design`, `Stmt2`, or a fuelled executor
the meaning of the language.

The relation's store is extensional. It contains declared scalar values,
memory identities and addressed memory cells, aggregate cells, and the
pending semantic queues needed by a slot. Executor caches such as compiled
driver lists and scalar arrays stay inside `CoreMemState` and are connected by
an explicit observation/embedding map. A relation proof therefore cannot
depend on a cache layout or on a source-order fold that happens to implement
the executor.

## Seven settled agreements and their status

1. **One parser-native relation.** The final relation matches PStmt, PExpr,
   PLhs, processes, memory declarations, regions, and continuations directly.
   Existing E-core-0/E-core-1 relations and the cursor relations are source
   material and bridge seams. Stmt2 lowering, cell expansion, and generate
   unrolling are never semantic definitions.
2. **The executor is an implementation.** A successful executor result needs
   a kernel-checked soundness theorem into the relation. Completeness and
   uniqueness are separate theorems for admitted classes. An existential
   fuel wrapper is an implementation witness, never the normative definition.
3. **Three semantic outcomes.** A finite derivation can complete or reach a
   loud language refusal. An infinite derivation is nontermination and has no
   settled result. Executor budget exhaustion is a fourth implementation
   outcome only. It is not refusal and it is not nontermination.
4. **Exactly one x rule.** At every permitted x or z decision read, the
   relation admits every 0/1 resolution independently for that read. The
   theorem quantifies over all such choices. This is the owner's per-read
   x principle from 2026-11-11 and 2026-11-24. The relation does not add
   origin correlation, simulator optimism, or a new unknown kind.
5. **Granularity is a parameter.** The relation carries
   `Granularity.process` or `Granularity.statement`. The owner has not
   chosen between them. The statement profile permits clause 4.7 preemption at
   source statement boundaries. The process profile makes one activation
   atomic. A mover or reduction theorem may derive the process profile from
   the statement profile for noninterfering processes, but neither profile is
   silently substituted for the other.
6. **Five obligations stay separate.** Soundness, finite completeness,
   schedule independence on observations, progress to a settled boundary, and
   trace inclusion have distinct statements and failure modes.
7. **No new timing or hardware layer here.** The decided clock-crossing,
   timing, environment, and x boundaries are inputs to this relation.
   Multiple clocks enter as one input event batch. Delays, metastability,
   memory macros, synthesis inspection, and other hardware-layer concerns
   remain outside this document.

## Existing slot definitions and their fate

The checkout's broader semantic inventory is useful when auditing migration.
M0 (`Semantics.lean`), S1 (`Scheduler.lean`), R1 (`Slot.lean` and
`Regions.lean`), the lowered `Design2`/`run2` stack, `MemCycle`, E-core-0/1,
and canonical E over `CoreMemDesign` are distinct stacks over different ASTs
and state representations. The table below records their fate. None of the
bounded enumerators or executor functions is promoted merely because it is
already executable.

| Existing definition | What it actually covers | Fate |
| --- | --- | --- |
| `Core0E.step`, `Steps`, `SlotCloses` in `Kernel/Core0E.lean` and `Core0Comb.lean` | Fuel-free relation over the lowered `Stmt2`, assigns and a limited combinational profile, process-atomic | Bridge and proof precedent. Transport its results to the parser-native relation, then retire or retain as a compatibility shell |
| `Core1Edge.step1`, `Steps1`, `SlotCloses1` in `Kernel/Core1Edge.lean` | Fuel-free relation over `Stmt2` edge bodies and NBA queues, process-atomic | Bridge and proof precedent. It is not the memory-capable normative relation |
| `Scheduler.oneStep`, `Steps`, `Slot`, `Run` | Choice-bearing relation over the older scalar `Design`, with statement actions and a bounded enumerator | Test and migration reference only. It is isolated to `Tests.lean` and `EdgePhaseConfluence.lean`, and is deleted or reduced to a compatibility wrapper after transport |
| `Sem2Ast`, `run2`, `Runs2`, `Models2` | A separate lowered semantic tier and executor surface. `Runs2` is existential fuel and `Stmt2` unrolls procedural loops | Compatibility executor. Add relation transport, preserve concrete checks, then retire duplicate meaning |
| `CoreMemDesign.step`, `runCoreMemRows` | The canonical memory-capable function, with statement, loop, settle, edge, and quiescence budgets | Executor only. Parameterize its limits and prove soundness and admitted-fragment completeness |
| `CombPhaseStep`, `EdgePhaseStep` in `CoreMemResume.lean` | Parser-shaped cursors and phase transitions, currently calling bounded executor leaves | Basis for the small-step relation. Replace executor leaves with relation steps, retaining cursor cut/resume lemmas |
| `EdgeConfluence.lean` and `EdgePhaseConfluence.lean` | Guarded frame, diamond, progress, queue, observation, and executor bridges for narrow NBA classes | Bridge library. Their current theorem statements remain useful and must not be described as whole-language confluence |
| `SeqRunsOn`, `SeqRunsM`, `SeqRunsI` in `SeqCycleRuns.lean` | Public clocked claims whose successful traces come from `runCoreMemRows` | Relation-first transport surface. Keep concrete cycle functions and checks, change the semantic premise |
| `MemE` and other duplicate memory routes | Separate memory executor and observation route | Bridge only while canonical memory transport is proved, then retire rather than add another semantics |

The old scheduler is not the authority for the final relation. Its
`ScheduleConfluence` theorem is an abstract lemma and its bounded
`allSlots` enumerator is a test tool. The canonical source-shaped phase
relations are the correct construction seam.

## Semantic values, refusals, and the three outcomes

The relation uses an extensional `SvStore` for semantic state and the
parser-native elaboration carried by `CoreMemDesign`. The executor's
`CoreMemState` is related to that store by an embedding and observation map.
A semantic refusal records the parser node and the applicable clause.

```lean
inductive RelRefusal where
  | unsupported (node : String) (clause : String) (detail : String)
  | illFormed (detail : String)

inductive RelOutcome (α : Type) where
  | completed (value : α)
  | refused (reason : RelRefusal)
  | diverged
```

`RelOutcome.diverged` is a view of an infinite path, not a constructor
that can be produced by a finite evaluator. The finite relation has completion
and refusal derivations. A missing rule cannot make a safety theorem vacuous.
For every semantic judgment we will prove a progress-or-refusal theorem, or
state the exact unsupported boundary.

The implementation keeps its current result distinction
`Res.ok`, `Res.timeout`, and `Res.unsupported` until the executor is
migrated. `timeout` means implementation budget exhaustion. A quiescence
loop returning `unsupported` for a budget exhaustion is an executor bug to
repair, not a semantic refusal. A true unsupported parser node maps to
`RelRefusal.unsupported`. An invalid schedule supplied by an external
enumerator is a separate validation result. It is not a legal relation path,
and it must not be reported as either a language refusal or budget exhaustion.
The typed relation constructs only legal transitions. A schedule adapter that
accepts an untrusted list must expose an `invalidSchedule` result before
invoking the relation.

## Judgment forms over PStmt and CoreMemDesign

These are the proposed public signatures. They are intentionally independent
of fuel and chosen schedule counters.

```lean
inductive Granularity
  | process
  | statement

structure XResolution where
  read : Nat → Bool

structure SvStore where
  scalar : String → LVec
  memory : String → Int → LVec
  aggregate : String → Option LVec

structure StmtState where
  env : IEnv
  store : SvStore
  locals : SvState
  scalarQ : NbaQueue2
  memoryQ : MemNbaQueue

inductive ExprRel
    (E : CoreMemDesign) (x : XResolution) :
    IEnv → SvStore → SvState → PExpr → LVec → Prop

inductive LhsRel
    (E : CoreMemDesign) (x : XResolution) :
    IEnv → SvStore → SvState → PLhs → LhsTarget → Prop

inductive StmtStep
    (E : CoreMemDesign) (g : Granularity) (x : XResolution) :
    StmtState → PStmt → StmtState → Prop

def StmtRun
    (E : CoreMemDesign) (g : Granularity) (x : XResolution)
    (start : StmtState) (finish : StmtState) : Prop :=
  Relation.ReflTransGen (fun a b =>
    ∃ p, StmtStep E g x a p b) start finish

structure SlotState where
  input : SvState
  region : Region
  machine : SvStore
  active : List EdgeCursor
  comb : List CombCursor
  scalarQ : NbaQueue2
  memoryQ : MemNbaQueue
  refusal : Option RelRefusal

inductive RegionStep
    (E : CoreMemDesign) (g : Granularity) (x : XResolution) :
    SlotState → SlotState → Prop

def SlotRun
    (E : CoreMemDesign) (g : Granularity) (x : XResolution)
    (start finish : SlotState) : Prop :=
  Relation.ReflTransGen (RegionStep E g x) start finish ∧
    (SlotQuiet finish ∨ SlotRefused finish)

structure InputBatch where
  time : Nat
  changes : List (String × LVec)
  edges : List (String × Edge)
  nodup : (changes.map Prod.fst ++ edges.map Prod.fst).Nodup

structure ObsState where
  time : Nat
  scalar : SvState
  memory : MemV

def Run
    (E : CoreMemDesign) (g : Granularity) (x : XResolution)
    (init : SlotState) (inputs : List InputBatch)
    (trace : List ObsState) : Prop := ...

def Diverges
    (step : α → α → Prop) (start : α) : Prop :=
  ∀ n, ∃ s, Relation.ReflTransGen step start s ∧ ¬Terminal s
```

The actual relation will use the existing cursor fields and memory identities
rather than introduce a second lowered statement language. The `...` in
`Run` and `Diverges` marks the remaining design work, not an admitted
axiom or a definition to use before the relation is implemented.

Expression constructors follow the parser node that they interpret. LHS
resolution carries declaration identity, dynamic index resolution, and written
bit masks. A block pushes its source-shaped tail. An `if` and `case`
select every relation-permitted arm. A `for` loop has a false-condition
completion rule and a true-condition body-then-loop rule, with no unrolling of
the PStmt. Blocking assignments update the current state. Nonblocking
assignments capture RHS and target at issue and enqueue an NBA record.

## x and z relation rule

At each read that the IEEE semantics leaves unresolved, `XResolution.read`
supplies either 0 or 1. The relation quantifies over every admissible
resolution at every such read. This includes a decision in an `if`, a case
item or dynamic index where the decided x principle says the choice is open,
and an x converted at the language boundary. A theorem that needs one result
must prove that all permitted reads give the same observation, or state a
known-value precondition. No `condTrue` branch is a semantic rule.

The decided environment rule treats external unknowns as real input bits.
Clock crossings and timing remain at the hardware boundary. The relation does
not invent an origin-correlated unknown, a metastability value, or a simulator
policy.

## Construct rules and IEEE clauses

* **Expressions.** Each `PExpr` node has its own rule. Four-state arithmetic,
  logical, bitwise, select, concatenation, replication, and conditional
  operations follow §§6.3.1, 11.4, 11.5, 11.8, and 11.4.11. Case equality and
  wildcard matching follow §12.5. An unimplemented expression derives a
  refusal naming its node and clause.
* **Blocking and nonblocking assignment.** A blocking RHS and target are
  evaluated at its selected statement event and update the current machine.
  An NBA RHS and target are sampled when issued and committed in the NBA region,
  preserving process order required by §10.4.2.
* **Blocks, branches, and loops.** Blocks execute parser statements in their
  source order within one process. `if`, `case`, and `for` use their
  source nodes. The `for` rules follow §12.7 and do not unroll a parameterized
  loop. A nonterminating loop has no finite completion derivation.
* **Processes and sensitivity.** Activation, waiting, and self-sensitivity
  follow §§9.2 and 9.4.2. A process is not sensitive to a signal while it is
  executing. An NBA update may enqueue a later same-slot activation.
* **Regions and events.** Active, inactive, NBA, reactive, and postponed
  transitions follow §§4.4–4.7, 4.9.4, and 10.4.2 to the extent the current
  profile admits them. A legal event order is a relation transition, not a
  list-head convention.
* **Memory and aggregates.** A memory NBA retains declaration identity,
  resolved index, issue-time value, and written mask under §11.5.1. Only
  unconstrained orders of disjoint footprints may commute. Within-process order
  and NBA capture order are fixed.
* **Unsupported constructs.** A construct without a rule has a refusal
  outcome. It is never approximated by a neighboring construct or a default
  value.

The semantic outcome set is therefore completed, refused, or diverged. An
executor-facing adapter additionally distinguishes budget exhaustion and an
invalid supplied schedule. These implementation and validation outcomes never
become semantic derivations.

## Granularity parameter

`Granularity.statement` exposes the fine-grained clause 4.7 relation, with
preemption only at parser statement boundaries and with source order inside
one statement. `Granularity.process` exposes an atomic activation profile,
which is useful for the current process-atomic E-core results. The profile is
not a semantic shortcut: a process-atomic theorem requires either a declared
profile assumption or a mover/reduction theorem proving that the statement
relation has the same observations.

The confluence theorem must therefore be parameterized:

```lean
theorem terminal_observable_unique
    (g : Granularity)
    (hguard : AdmittedConfluent E g)
    (h₁ : SlotRun E g x₁ s t₁)
    (h₂ : SlotRun E g x₂ s t₂)
    (hsameInput : SameExternalBatch x₁ x₂) :
    Observe E t₁ = Observe E t₂
```

The current `edgesV_order`, `EdgePhaseStep.two_nba_observable_diamond`,
and `EdgePhaseTerminalPath.observable_confluent` are process- or cursor-level
results with explicit admissions. They do not prove the statement-granular
whole-slot theorem. The owner decision on the default `g` remains pending.

## Simultaneous events and observations

One macrostep consumes an `InputBatch`, not a serial list of single-edge
steps. For

```systemverilog
always @(posedge clk_a) a <= b;
always @(posedge clk_b) b <= a;
```

from `a = 0, b = 1`, a batch containing both edges enables both processes
before either NBA commit. The relation contains the result `a = 1, b = 0`.
A batch containing only one edge is a different external history and may
produce `(1,1)` or `(0,0)` after the other edge arrives.

An edge caused by an NBA update later in the same timestamp remains causally
later in the relation. It is not merged into the external batch. If an input
change and an edge activation share a timestamp, both are events in the batch
and every legal active-event order is represented. The current
`CoreMemDesign.step` applies all inputs before edge execution, so its
implementation bridge has a known gap for the standard order in which a
process runs before that input update.

The observation boundary is settled end-of-slot scalar values and committed
memory views. A theorem may additionally expose edge-sampled values. Equality
of final output bits alone is not enough for a refinement equivalence. The
equivalence must preserve state facts needed by future slots.

The acceptance witness in
`Examples/system-verilog/sem2/simultaneous_nba/` runs the source and its
clean-room testbench from `(a,b) = (0,1)`. The four measured rows are the
initial state `(0,1)`, an A-only edge `(1,1)`, a B-only edge `(0,0)` from a
fresh `(0,1)` state, and a simultaneous A+B batch `(1,0)`. Icarus Verilog
13.0 and Xcelium 24.03-s004 both report all four rows as MATCH. The
simultaneous result is therefore neither serial result, and a relation whose
step accepts only one edge would omit a legal behavior. The fixture is an
oracle receipt only. It does not choose an event order for the normative
relation or change the executor.

## Five independent bridge obligations

1. **Soundness.** If the executor returns `.ok s'`, some relation execution
   reaches a state whose observation is `s'`. This is not proved for the
   complete canonical E route. The current per-path theorem
   `EdgePhaseTerminalPath.executor_result_memory` is a narrow receipt-based
   instance.
2. **Finite completeness.** Every finite relation execution in an admitted
   fragment is reproduced by some schedule and sufficiently large executor
   limits. No fixed 4096 value belongs in this theorem. This is open.
3. **Schedule independence on observations.** Two executions under the same
   external input history have equal observations for a proved confluence
   class. The scalar and memory queue permutation results and the fine-grained
   memory diamond are partial instances. This is open for the complete slot.
4. **Progress.** Every allowed internal execution of an admitted macrostep
   reaches its settled boundary under its stated assumptions. The abstract
   `ScheduleConfluence.terminal_exists` and scalar phase progress lemmas are
   scaffolding. The memory-aware edge admission now has a concrete cursor
   measure, next-step, and finite-terminal-path theorem, still only for its
   stable-state and empty-continuation premises. Zero-time divergence is not
   silently discarded.
5. **Trace inclusion.** The executor's input-and-observation trace is a trace
   of the relation. `executor_trace_inclusion_singleton` is a one-row
   admitted-NBA package. Full multi-row canonical-E trace inclusion is open.

A deterministic executor can satisfy soundness while failing independence or
progress. Universal user claims require the obligations named by the claim.

## Three user levels and the first executable bridge

The reference level is the small-step relation over configurations containing
the current parser node, continuation, region, pending scalar and memory
updates, and the settled observation. It exposes every permitted event order
and every per-read x resolution. `StmtRun` and `SlotRun` are reflexive-
transitive closures of those steps. This is the level at which clause 4.7
preemption and zero-time divergence are stated.

The macrostep level is derived for a certified profile. It consumes one
`InputBatch` and returns a settled state, with separate soundness, progress,
and schedule-independence theorems. Its state equivalence must preserve the
facts needed by later batches, including declaration identity, pending
causes, and memory observations. Equal output bits alone are insufficient.

The trace and contract level quantifies over input histories and initial
states. Assumptions such as clock progress, reset release, fairness, and the
absence of zero-time divergence are explicit hypotheses of liveness claims.
Module contracts compose through the macrostep refinement theorem and never
silently replace the reference relation.

The cheap first bridge is an implementation relation, not the meaning:

```lean
def ExecStep
    (exec : Nat → CoreMemState → InputBatch → Res CoreMemState)
    (input : InputBatch) (s s' : CoreMemState) : Prop :=
  ∃ fuel, exec fuel s input = .ok s'
```

The actual executor API currently exposes `CoreMemDesign.step` without this
explicit argument, while its internal workers carry implementation limits.
The displayed signature is therefore the abstract adapter to introduce when
those limits are made explicit. The bridge is justified only by the proved
fuel-monotonicity theorem and an executor soundness theorem. It must be
replaced construct by construct by the rule-based `SlotRun` relation. A finite
relational derivation is then reproduced by some schedule and a sufficiently
large implementation limit, while a timeout remains an implementation result
rather than a semantic outcome. No user theorem may mention `fuel`, `need`, or
the implementation limit.

## Footprints and constrained ordering

Every write carries a footprint consisting of declaration identity, memory
identity when applicable, resolved address, and written bit mask. Scalar
variables are the one-cell case. The relation preserves ordering that IEEE
1800 requires, including source order within one process and the issue-time
capture of an NBA right-hand side and target under §10.4.2. Only updates with
provably disjoint footprints may commute. A single commuting-update lemma is
used for scalar and memory updates. Dynamic addresses require an invariant
proving disjointness or aliasing, and are never treated as distinct merely
because their syntax differs.

## Relation construction and the existing successor function

The rule presentation above is the readable specification. The eventual Lean
implementation should define its small-step relation by membership in a
source-shaped successor function where that function is already exact, using
lemmas of the form `nextStates_iff`. This avoids maintaining two independent
copies of the rules. `Scheduler.mem_nextStates_iff` is the existing model for
this style, but its older scalar state is a migration reference only. The
parser-native successor function must retain `PStmt`/`PExpr`/`PLhs`, memory
identity, regions, and continuation frames, and it must expose refusal rather
than silently return an empty successor set.

## Relation design against the simulation-semantics literature

Andreas Loow, *The Simulation Semantics of Synthesisable Verilog*, OOPSLA
2025, arXiv:2502.19348, documents tensions between IEEE scheduling clauses
and common synthesis-oriented executable models. This design follows the
standard's clause 4.6 region transitions, clause 4.7 event ordering, clause
4.9.4 wakeups, and §10.4.2 NBA capture as the normative relation. It keeps
the implementation's narrower certified profiles as derived macrosteps and
refuses or leaves unproved any construct outside those profiles. It does not
resolve a standards-versus-practice discrepancy by changing the language
meaning. Any concrete contradiction exposed by a differential or proof
receipt must be recorded as a finding with a reproducer and escalated for an
owner decision.

## Current bridge inventory

### Frame-lemma audit

The first diamond ingredients are present on the real evaluator. The
parser-native closure theorem
`CoreMemDesign.edge_readsV_eq_instantiated_idents_of_pure` identifies
`readsV` with the instantiated evaluator identifier set for pure expressions.
`edge_evalExprLocals_frame_of_parser_closure` and
`edge_evalExprLocals_frame_of_driver_closure` then transport a closure guard
to `evalExprLocals`, including the actual `setScalarState` write used by the
executor. The corresponding two-expression theorem
`edge_evalExprLocals_two_expr_cross_write_frame_of_driver_closure` frames each
reader against the other process's write.

The write-side theorem
`edge_setScalarState_commute_of_disjoint` proves commutation of two concrete
scalar writes from `Coherent` state and distinct declaration identities.
`edge_evalExprLocals_two_write_frame_of_driver_closure` combines that write
footprint with the evaluator frame. These are kernel-checked frame facts, not
the scheduler diamond itself. They still require the pure-expression and
function-free premises, explicit closure coverage, coherent state, and
declaration disjointness. Memory footprints, dynamic aliasing, process
progress, and the bridge from every fine-grained slot path to `step` remain
separate obligations.

The following results are real and intentionally narrow.

* `readsV_eq_instExpr2_idents_of_pure`,
  `evalExprLocals_congr_readsV_of_pure`, and scalar write lemmas are frame
  lemmas over the real evaluator and write functions.
* `edgesV_order`, `edgesV_perm_memory`, and `edge_schedule_refines_step_memory`
  are source-order permutation bridges with explicit evaluator and memory
  receipts.
* `EdgePhaseStep.two_nba_memory_observable_diamond` is a local fine-grained
  memory diamond with a view-level decode receipt.
* `EdgePhaseTerminalPath.memory_queue_trace` and `memory_queue_perm` give
  terminal queue permutation under explicit memory admission.
  `scalar_queue_perm_memory` gives the corresponding scalar queue permutation
  when those cursors also issue memory NBAs.
  `EdgePhaseStep.memory_measure_decreases`, `memory_progress`, and
  `EdgePhaseTerminalPath.memory_exists` provide the corresponding finite
  scheduler-progress bridge, and `memory_length_balance` gives its exact
  cursor bound. They do not establish commit success or an observation
  result.
  `memory_state_eq`, `memory_view_eq_of_trace`, and
  `memory_commit_success_of_decode` expose state, view, and canonical commit
  facts per path.
* `memory_commit_observation_eq_of_perm` compares successful canonical
  commits under identity-preserving decode, coherence, pairwise-disjoint
  footprints, and successful commit receipts.
* `EdgePhaseTerminalPath.executor_result_memory` connects one memory-aware
  terminal path to `CoreMemDesign.step`, retaining every settle, edge-run,
  commit, post-settle, and quiescence receipt.
* `EdgePhaseTerminalPath.memory_confluence_refines_step` combines the
  memory-queue permutation observation with that executor bridge. It proves
  decoded, pairwise-disjoint memory views agree across terminal paths while
  retaining the selected path's exact E receipts.
* `EdgePhaseTerminalPath.memory_canonical_confluence_refines_step` adds the
  canonical `MemState.commitNba` form. Every terminal path supplies its own
  successful commit, decode identity, and `RecOk` receipts, and its `E.memOf`
  observation is compared with the selected executor path.
* `EdgePhaseTerminalPath.observable_confluent` and
  `confluence_refines_step` are scalar or admitted-NBA path results. They do
  not establish the whole relation.

The clean-room `edge_order_memory_e` envelope is a concrete memory-NBA
receipt. Its `N = 4` load reports four processes and `seqOblIM = true`, and
`agree.lean` exercises the memory-leaf and procedural-loop frame adapters plus
`step_seqIM`. Its differential test reports three matching post-edge rows on
Icarus Verilog 13.0 and Xcelium 24.03-s004. The receipt keeps the evaluator
and declaration-identity premises explicit, so it does not turn this fixture
into a whole-design confluence theorem.

The clean-room `fsm_logic_confluence_e` envelope is a third source-shaped
NBA witness. It has one case-based state process and two continuous-assignment
drivers. Its `fsm_nba_confluence` theorem instantiates the same guarded
terminal-path-to-`CoreMemDesign.step` bridge, and its six startup/reset/state
rows match Icarus Verilog 13.0 and Xcelium 24.03-s004. The logic-coded state
avoids a separate enum elaboration rule so this receipt tests the scheduler
class rather than enum ingestion.

These are bridge-only results. They do not establish full canonical-E
soundness, arbitrary aliasing, mixed macrostep trace inclusion, zero-time
liveness, or an owner-selected default granularity.

## User-facing statements

The relation-first user surface quantifies over all admissible initial states,
input batches, schedules, and per-read x resolutions. Totality is stated
separately when a property needs a settled result.

```lean
def AllRuns (E : CoreMemDesign) (g : Granularity)
    (P : List ObsState → Prop) : Prop :=
  ∀ init, AdmissibleInit E init →
  ∀ x inputs trace, ValidInputs inputs →
    Run E g x (Initial E init) inputs trace → P trace

def Total (E : CoreMemDesign) (g : Granularity) : Prop :=
  ∀ init, AdmissibleInit E init →
  ∀ x inputs, ValidInputs inputs →
    ∃ trace, Run E g x (Initial E init) inputs trace
```

A two-flop synchronizer statement is conditional on the actual admission
guards and quantifies over every schedule:

```lean
theorem sync_two_flop_relational
    (hdesign : SyncAdmitted E g) :
    ∀ init x inputs t₁ t₂,
      Run E g x (Initial E init) inputs t₁ →
      Run E g x (Initial E init) inputs t₂ →
      observable E t₁ = observable E t₂ ∧
      syncInvariant t₁ ∧ syncInvariant t₂ := by
  ...
```

A memory FIFO reset-loop statement retains the parameterized loop and its
memory footprints:

```lean
theorem fifo_reset_loop_relational
    (hdesign : FifoMemoryAdmitted E g)
    (hreset : ResetBatch inputs) :
    ∀ init x trace,
      coherent init →
      Run E g x (Initial E init) inputs trace →
      ∀ k, 0 ≤ k → k < depth →
        memoryView (last trace) k = zero ∧
        fifoInvariant (last trace) := by
  ...
```

A design with several legal terminal observations states a permitted set rather
than asserting uniqueness. Liveness assumptions such as clock progress, reset
release, fairness, and absence of zero-time divergence are hypotheses, not
consequences of a completed executor call.

## Transport for existing claims

The five interface lemmas in `SeqCycleStep.lean` are the migration seam. Add
relation-first counterparts without changing the design-specific cycle
functions.

```lean
def RelSeqRunsOn {α}
    (E : CoreMemDesign) (g : Granularity)
    (rowsOf : α → List InputBatch) (Ok : α → Prop)
    (P : α → List ObsState → Prop) : Prop :=
  ∀ init, AdmissibleInit E init →
  ∀ a, Ok a → ValidInputs (rowsOf a) →
  ∀ x trace, Run E g x (Initial E init) (rowsOf a) trace →
    P a trace

theorem SeqRunsOn_to_RelSeqRunsOn
    (h : SeqRunsOn r rowsOf Ok P)
    (hsound : ExecutorSound E g) :
    RelSeqRunsOn E g rowsOf Ok P

theorem RelSeqRunsOn_to_SeqRunsOn
    (h : RelSeqRunsOn E g rowsOf Ok P)
    (hcomplete : ExecutorComplete E g) :
    SeqRunsOn r rowsOf Ok P
```

The analogous `RelSeqRunsM` and `RelSeqRunsI` preserve memory views and
multi-clock instants. `SeqRunsOn` currently uses `runCoreMemRows` and a
fixed-budget `CoreMemDesign.step`, so it stays an executor compatibility
surface until both adapters exist.

For the combinational judgment, transport `Models2` and `Runs2` through
the relation's `CombRun` and its settle theorem:

```lean
theorem Models2_to_RelComb
    (hmodel : Models2 d P)
    (hterm : Terminates2 d)
    (htransport : CombExecutorIncluded E d) :
    RelCombModels E P

theorem RelComb_to_Models2
    (hrel : RelCombModels E P)
    (hcomplete : CombExecutorComplete E d) :
    Models2 d P
```

The `Models2` and `SeqRuns*` adapters carry explicit known-decision,
coherence, and input-width hypotheses. Existing statements that use
`condTrue` to turn an x into the else branch, including the reset-loop and
register-memory examples identified by the proposal audit, must be restated
with a known-value premise or a permitted-outcome postcondition. Concrete
`#guard` differential rows remain executor checks.

## Fact check of the proposals

The five proposals agree on the architecture, but the factual map was checked
against this checkout.

* The existing E-core-0 and E-core-1 relations are real. `Core0E.lean`
  exposes `step`, `Steps`, and `SlotCloses`; `Core1Edge.lean` exposes
  `step1`, `Steps1`, and `SlotCloses1`. They are over `Elab`/`Elab1`
  and lowered `Stmt2`, with process-atomic choices, so they are precedents
  and bridges rather than the final PStmt relation.
* `Scheduler.lean` is isolated in the current import graph. Its
  `SchedulerDesign` uses the old scalar `Design`, and its bounded
  enumerators are test instruments. It is not the canonical memory route.
* `SeqRunsOn`, `SeqRunsM`, and `SeqRunsI` are definitions in
  `SeqCycleRuns.lean` whose rows ultimately call `runCoreMemRows`.
  Their theorem heads hide implementation limits.
* `forValues2` computes the parameterized header value list structurally in
  `Param2.lean`. The visible `N ≤ 4000` condition comes from
  `PStmt.need ≤ 4096` in `SeqCycle.lean`, not from a language bound.
* The quiescence route in `CoreMemExec.lean` has executor paths that return
  `.unsupported` on exhaustion. That message must be separated from a
  semantic refusal.
* The race-guard transitive closures use a literal 32-hop argument in
  `CoreMemExec.lean`. This is a confirmed admission bug and is fixed by the
  executor lane's 775472220; it is not a relational theorem.
* `XResolve.lean` contains the legacy correlated `Resolves` relation and
  the per-read `XRead`/`XReadRun` relation. The latter is the authority
  under the owner's ruling. Existing executor uses of `condTrue` are not a
  formal x semantics.
  The proposals that recommend origin-correlated unknowns conflict with the
  owner's fixed per-read decision and are not adopted here.
* `EdgePhaseConfluence.lean` imports `Scheduler.lean` for historical
  witnesses. This does not make the old Scheduler relation the authority.
* Existing memory and phase confluence theorems require explicit admissions,
  queue/frame receipts, and in several cases process-atomic or cursor-local
  assumptions. They must not be described as whole-design confluence.

## Migration order

The first stage belongs to the executor lane and starts by removing
implementation budgets from semantic/user theorem paths.

### S0 — executor de-fuelling and audit

1. Replace fixed statement, LHS, loop, generate, automatic-name, and
   settle parameters with explicit `ExecLimits` in implementation APIs.
2. Remove the user-facing `PStmt.need ≤ 4096` and the derived `N ≤ 4000`
   hypotheses. Keep any implementation limit in executor-only theorem names.
3. Make pure walkers and finite header computation structural. Repair the
   32-hop closure truncation and classify loop-header integer overflow loudly.
4. Distinguish executor `.timeout` from semantic refusal and test a
   memory-only quiescence loop.
5. Add fuel monotonicity and finite-run threshold lemmas. This stage is owned
   by ls-sv2 and must land before relation implementation.

### S1 — parser-native relation core

Add the expression, LHS, statement, process, region, slot, refusal, and
divergence judgments above. Each constructor cites its IEEE clause and gets a
differential row or an explicit no-oracle refusal row. Keep both granularity
parameters available.

### S2 — executor soundness

Prove that every successful `stepFuel` result is a relation run for a
legal resolution and input order. Audit every executor shortcut, including
inputs-first ordering, edge tests, empty-row behavior, and x-optimistic
branches. Executor admission guards are implementation filters and are not
semantic refusals.

### S3 — admitted confluence and progress

Prove frame lemmas over `evalExprLocals` and real writes, then local diamonds
from the guards. Add memory footprints, loops, dynamic-address invariants,
and the fine-grained-to-process mover theorem. Establish observation
independence and progress for the smallest admitted NBA plus continuous-assign
class before widening.

### S4 — run and user surfaces

Add `RelSeqRunsOn`, `RelSeqRunsM`, `RelSeqRunsI`, combinational transport,
totality, and invariant/refinement surfaces. Migrate the seq_cycle examples
and the `Models2) records through generic adapters. Keep differential
`#guard` rows.

### S5 — one semantics and retirement

Once transport is proved, retire duplicate meanings. Delete or reduce
`Scheduler.lean`, `MemE), and lowered E-core semantic shells according to
their transport results. Keep only compatibility wrappers and executor/test
tools. No new semantic island is added.

## Risks and failure modes

* A missing relation constructor can make a universal theorem vacuous. Every
  relation layer needs progress-or-refusal and totality/no-refusal lemmas.
* Independent x resolutions can change a theorem's meaning. The x census must
  precede migration, and known-decision hypotheses must be explicit.
* Statement-granular preemption may differ from process-atomic behavior.
  Granularity stays explicit until the owner chooses a default, and mover
  proofs must carry the equivalence used by future slots.
* Fixed executor limits can masquerade as language bounds. Static searches
  and `ExecLimits) keep them out of relation and user statements.
* A relation with all regions at once can become unprovable. Start from the
  current PStmt and cursor seam, add only admitted regions, and refuse the
  rest.
* Differential membership checks can hide wrong answers. Equality rows remain
  mandatory when all decisions are known; membership rows record all allowed
  outcomes when the standard leaves a choice open.

## Proposed engineering-rule line

> Define SystemVerilog's normative meaning as a fuel-free relation over
> parser-native PStmt/PExpr/PLhs nodes, memory identities, scheduler regions,
> every legal event order, and every per-read x/z resolution allowed by IEEE
> 1800. An executable function is an implementation and requires a
> kernel-checked soundness theorem to that relation. Fuel may occur only in
> implementation judgments and their bridges. Granularity must be an explicit
> parameter until its profile is decided. User theorems quantify over every
> legal input, schedule, and resolution. Unsupported constructs refuse
> loudly, and nonterminating constructs have no fabricated settled result.

