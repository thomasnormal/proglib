# Procedural combinational equation contract

This contract is the admission boundary for a source-shaped `always_comb` or
`always @*` body whose effect is to compute combinational equations. It is
derived from the retained parser nodes and from E's `execCombStmtFuel` walk.
It does not give the body a second meaning and it does not lower the source
before the E semantics runs.

The contract covers a body made of source-order blocking assignments, blocks,
`if` statements, and plain `case` statements with their parser-selected
`case`, `casez`, or `casex` mode. The currently admitted target and expression
forms are exactly the forms accepted by the corresponding E executor. A
target or expression outside that executor's admitted fragment is a loud
refusal. Procedural `for` is a later extension of this contract and is not
silently treated as an unrolled list.

## Equation extraction

For a pre-state `σ` and external inputs `ι`, E evaluates the retained body
node for node. The evaluator carries the current store through the statement
list. A blocking assignment evaluates its right-hand side in that current
store, then updates its target before the next source statement. Consequently
an assignment after an earlier assignment sees the earlier value. The
equation for a written signal is the final value produced by this walk,
expressed over the pre-state and inputs.

An `if` keeps an equation for each branch and joins them with the exact E
truthiness operation. An absent `else` keeps the pre-state value on its empty
path. A `case` evaluates the subject and item expressions in source order,
uses the parser's case mode and `caseHit`, and selects the first matching arm.
An unmatched case uses its `default` arm when present and otherwise keeps the
pre-state value. The resulting equation is a source-order conditional
expression. This representation records the node's control flow; it is not a
rewrite of the program into a chain of `if`s or into a continuous assignment.

The extraction returns one equation for every written window. A signal written
by several source assignments therefore has one final equation, with the
earlier writes substituted at the later read sites. A write to a sub-window
is retained as a window update. The equation relation includes the declared
width and the exact four-state `LVec` value, including `x` and `z`.

The control and value rules are the rules of IEEE 1800-2023 §9.2.2.2 and
§9.2.2.2.1 for `always_comb`, §9.4.2.2.2 for the implicit event control of
`always @*`, §10.4.2 for blocking assignment ordering, §12.4 for `if`, and
§12.5 for `case`. No Boolean approximation is introduced for an unknown
condition or selector.

## Admissibility

The equation profile accepts a body only when all of the following hold.

* Every written window is statically identified and has a declared width.
  The body has one effective writer for each window, and windows written by
  distinct processes are disjoint.
* Every written window receives a value on every control path. An unconditional
  default followed by a conditional sub-window override is complete. A path
  that leaves a final window at its pre-state value is a partial assignment
  and is refused as a latch shape.
* After symbolic execution, no final equation reads a window written by the
  same body. This includes a read before the first write and a value retained
  by an empty `if` or unmatched `case` arm. Such a self-read is refused even
  when one concrete run would happen to reach a fixed point.
* Every expression read is declared, every retained node is supported by the
  E evaluator, and the body has no nonblocking assignment, delay, wait, event
  control, unsupported statement, or unresolved dynamic target. Function calls,
  aggregate forms, and memory forms remain at their existing E boundaries
  unless their own source-shaped contract is present.

The refusals are part of the contract. In particular, the loader never keeps
source text for a later parser, inserts a missing default, chooses one
schedule, or treats an x/z selector as a known Boolean. A refusal has no E
run and cannot be used as a vacuous premise of a design property.

## Refinement boundary

Let `D` be an admitted design whose procedural bodies satisfy this contract,
whose startup readiness is recorded by E, and whose inter-process read/write
windows have an acyclic rank. For every admitted initial state, input, and
legal scheduler resolution, every E execution that reaches quiescence has a
closed store `σ'` satisfying every extracted equation in `D`.

Conversely, every equation-preserving E activation is the result of the
source-shaped body walk at its activation state. Thus a quiescent E result and
the equation relation agree at the observation boundary. The theorem quantifies
over the scheduler's permitted process and event order. It does not pick a
convenient order or add a second combinational semantics. The rank and the
single-writer conditions are what make the equation result independent of the
order between otherwise enabled processes.

The startup premise is different for the two process kinds. `always_comb`
has its §9.2.2.2 startup activation and excludes variables written by the body
from the implicit sensitivity set under §9.2.2.2.1. Plain `always @*` starts
with its §9.4.2.2.2 event wait. A time-zero event or connection-order refusal
therefore remains a scheduler refusal rather than an equation theorem.

The contract is four-state. The equations retain E's `LVec` values and its
case and truthiness operations. The per-read X-E resolution relation and its
refinement theorem are separate work. When that relation is applied, a proof
must cover every permitted resolution at each IEEE decision point.

## Differential rows and next extension

The refinement packet must include source-shaped rows against Icarus Verilog
13.0 and Xcelium 24.03-s004. Selectors and data cover `0`, `1`, `x`, and `z`,
including the first activation and the default or unmatched paths. The rows
must run through E's retained envelope and compare each observation, rather
than compare a hand-written equation against a simulator transcript.

The next extension is a parser-retained procedural `for` node. Its equation
walk will sequence the loop iterations at the source node and will require a
static termination and write-window contract. It will not unroll a parametric
loop or hide a loop behind a generated list.

Until the refinement theorem and these rows land, `EquationGate` remains
closed for procedural combinational bodies. General `$error` and delay
controls remain separate refusals.
