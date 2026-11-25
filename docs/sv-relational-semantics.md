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

Executor soundness, race-free uniqueness, confluence, and acceptance examples
are subsequent T2-T4 work. They must state their admitted-fragment
hypotheses visibly and must quantify over every legal scheduling and oracle
choice.
