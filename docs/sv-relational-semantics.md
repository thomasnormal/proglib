# Relational semantics for SystemVerilog

This document records the T1 fuel-free relation for the admitted clocked
fragment. The relation is defined in
[`LeanModels/Sv/Kernel/NdStep.lean`](../LeanModels/Sv/Kernel/NdStep.lean).
The executor remains an implementation and differential-test instrument.

`ndStep` is the one authoritative step function. `Nd.Step` opens its cursor
choice and `Nd.Run` is the reflexive-transitive closure. A step has no fuel or
depth bound. `NdState.begin` applies one input row, and `Nd.EventSettles`
relates that start to a settled state.

## Choices and boundary

The scheduling choice is a cursor index. The relation permits every runnable
cursor at every parser-node boundary. Process-atomic runs can be derived by a
restriction, while the owner has not chosen the default granularity.

Unknown bits in an `if` condition are resolved by a consumed `Oracle`. Each
unknown bit consumes one fresh answer. `Oracle.read_xread` and
`Oracle.read_complete` connect this supply to the per-read `XRead` relation.

Admission is part of `ndStep`, so a non-admitted design produces a named
refusal even when callers invoke `Nd.Step` directly. The admitted design has
edge or explicit event processes, no continuous or combinational region, no
resolved net, no time-zero metadata, and no unsupported process.

The step refuses case equality and inequality, wildcard equality, `casex`,
`casez`, unknown write indices, x/z clocks and event expressions, and blocking
writes that move an event-source signal. The last refusal prevents the stale
wake-base wrong answer found by the WAKE-BASE differential receipt.

Ternary conditions and memory-read indices still use the existing four-state
merge. That merge is a superset until the owner decides whether those reads
become oracle sites. T4c, independent x reads twice in one expression, is
still open.

The leaf evaluator retains implementation budgets of 4096 in `resolveLhs2`
and `resolveConcatLhs2`. Its expressions use the existing `Expr2` lowering.
Elaboration's `iterFuel = 4096` remains outside the relation and is listed as
trust debt.

## Open owner questions

- scheduling granularity, statement-level or process-atomic
- x on clocks and event controls
- inputs-first ordering within one input row
- atomicity of the nonblocking commit
- the ternary and memory-index x rule
- the elaboration budget boundary

## Proof interfaces

`Nd.Run.invariant` is the unbounded induction principle. The event-level
variant is `Nd.EventSettles.invariant`. `ndStep_oracle_irrelevant` and
`ndStep_oracle_unchanged` provide the knownness interface. These theorems are
about the one step function and do not introduce a second semantic stack.

Because the step refuses x/z on a clock or event expression, `NdState.begin`
refuses from a power-on store whose clocks are x. Until the owner decides how
the first known clock value is modelled, the theorems below are about a start
store whose control signals are known, the named hypothesis
`CoreMemDesign.ControlsKnown`.

Executor soundness is `CoreMemDesign.step_sound` and its row-list form
`runCoreMemRows_sound` in
[`LeanModels/Sv/Kernel/NdSound.lean`](../LeanModels/Sv/Kernel/NdSound.lean).
On the syntactic fragment `CoreMemDesign.NbaClocked`, from a typed start store
with known controls, a result of the executor's slot function is the end of a
settled run of the relation under the executor's own choices: the first
runnable cursor to completion and the all-zero oracle. This is soundness for
those choices. It is not completeness. `Nd.Trace` is the multi-row closure
with the oracle threaded from row to row.

The footprint lemma is in
[`LeanModels/Sv/Kernel/NdConfluence.lean`](../LeanModels/Sv/Kernel/NdConfluence.lean).
`Nd.NonInterfering` is the condition on the cursors woken by one event: each
alone leaves the store unchanged and reads no unknown at a decision, their
nonblocking updates are pairwise disjoint, and none targets a clock or event
source. From it `Nd.settled_view` and `Nd.EventSettles.view_unique` derive
that every settled outcome has one scalar view, and `Nd.exists_settled` that
one exists. Uniqueness is of the observable scalar view, not of the whole
machine state.

The acceptance example is
[`simultaneous_nba/relation.lean`](../Examples/system-verilog/sem2/simultaneous_nba/relation.lean):
`swap_only`, `swap_exists`, `swap_unique`, the executor agreement
`swap_executor`, and `if_condition_x_read_twice_can_differ`. The two-flop
synchroniser, x read twice in one expression and the FIFO for every depth are
still open.
