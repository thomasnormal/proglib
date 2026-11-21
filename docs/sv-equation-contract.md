# Procedural combinational equation contract

This contract specifies the source-shaped combinational fragment before any
EquationGate admission. Its semantic authority is E-core-0, the event
semantics with a `ScheduleOracle` ranging over every legal process order. The
canonical-E executor in `CoreMemDesign` is an implementation under review. A
bridge from that executor to E-core-0 is required before a gate can use this
contract.

The contract applies to a retained `always_comb` or `always @*` body made from
blocking assignments, source-order blocks, `if`, and `case` nodes. A
procedural `for` node is outside this version. The body remains a parser node
throughout the semantic walk. No source text is reparsed and no body is
lowered to a list of continuous assignments.

## Equation extraction

For a pre-state `σ` and external inputs `ι`, execute the retained body node by
node under the exact four-state expression and statement rules. A blocking
assignment evaluates its right-hand side in the current store and then writes
its target. A later statement therefore observes an earlier blocking write.
The equation of a written window is the final value produced by this walk,
expressed as a relation between `σ`, `ι`, and the resulting store. The
relation preserves the declared width, signedness, state kind, and every
`LVec` bit, including `x` and `z`.

An `if` contributes the equations of its branches using the language's exact
truthiness rule. An absent `else` leaves the current value on that path. A
`case` evaluates its subject and item expressions in source order, applies the
parser-retained case mode and `caseHit`, and selects the first matching arm.
An unmatched case uses its `default` arm when present and otherwise leaves the
current value. The equation relation records this control flow directly. It
does not replace the node with another program.

The relevant IEEE 1800-2023 rules are §9.2.2.2 for `always_comb`, §9.2.2.2.1
for its implicit sensitivity exclusion, §9.2.2.2.2 for the comparison with
`always @*`, §9.4.2.2 for an implicit event control, §10.4.1 for blocking
assignment ordering, §12.4 for `if`, and §12.5 for `case`.

## Admissibility

A body satisfies this contract only when the following facts are established
from its retained nodes.

* Every target window is statically identified and has a declared type and
  width.
* Every written window receives a value on every control path. A path that
  leaves a final window at its incoming value is a partial-assignment latch
  shape and is refused.
* After the source walk is symbolically summarized, no final equation reads a
  window written by the same body. A read before its first write remains a
  self-read. A read after a write is permitted when substitution removes the
  body's own window from the final equation. An empty `if` path or unmatched
  `case` path that preserves the incoming value fails this condition.
* Every expression read is declared and every retained node is supported by
  the exact E expression evaluator. Nonblocking assignments, delay controls,
  waits, event controls, unsupported statements, unresolved dynamic targets,
  and procedural `for` nodes are loud refusals in this version.

The contract does not choose a value for an unknown condition or selector. It
also does not choose an active-region order. A refusal has no semantic run and
cannot be used as a vacuous premise of a property.

At the design level, separate obligations are needed for one effective writer
per window, disjoint windows between processes, and an acyclic rank of
inter-process dependencies. Those obligations are required by the
schedule-independent refinement theorem and are not inferred from one body.

## Process timing and the pending bridge

An `always_comb` body has its §9.2.2.2 startup activation. Its implicit
sensitivity excludes variables written by that body under §9.2.2.2.1. A plain
`always @*` begins in its §9.4.2.2 event wait and has no equivalent mandatory
time-zero activation. The two process kinds therefore need separate startup
premises. `always @*` remains outside any equation gate until its startup
behavior has differential rows from Xcelium.

The pending theorem must quantify over every legal E-core-0 schedule and state
that a quiescent result satisfies the extracted equations, with the converse
activation result at the same observation boundary. Its hypotheses must
include the body conditions above, the design-level writer and rank
certificates, and the process-specific startup premise. A second theorem must
show that canonical E's retained executor agrees with that E-core-0 result for
the same admitted loaded design. Neither theorem is asserted by this page.

## Differential obligations and next extension

The refinement packet needs a runner using Icarus Verilog 13.0 and Xcelium
24.03-s004. Its rows must exercise `if` and `case` selectors and labels at
multiple widths, `casez`, `casex`, x/z selectors and data, first activation,
default and no-match paths, bit and part-select targets with x indices, and
reads after writes. Rows compare the retained E envelope with each simulator.
A simulator discrepancy is recorded rather than resolved by choosing one
answer.

The next source-shaped extension is procedural `for`. Its contract must
sequence loop iterations at the node and prove a termination and write-window
condition. It must preserve parametric structure and must not unroll the loop
into generated statements.

EquationGate remains closed until the loaded-design theorem and the
canonical-E bridge have been proved and audited. General `$error` and delay
controls remain separate refusals.
