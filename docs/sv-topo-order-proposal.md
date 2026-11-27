# Topological order for continuous assignments

## TOPO-ORDER PROPOSAL

The current clocked route requires `CoreMemDesign.topoC`: every continuous
assignment reads no target of itself or of a later source-order assignment.
This is a sufficient condition for the existing `settleRaw` implementation,
which performs one source-order pass. It is not an arbitrary acyclicity test.

A natural shifter can have a dependency DAG whose parser/source order is not a
topological order. Accepting it by merely weakening `topoC` would be unsound:
a one-pass source-order settle can expose a stale intermediate value even
though the dependency graph has no cycle.

The proposed trusted-library change is therefore two-stage:

1. Keep the parser-native `PProcess.assign` list and the existing expression
   semantics. Define a source-shaped dependency graph from the names read by
each compiled assignment to its assigned target roots. Add a theorem that a
finite acyclic graph has a topological permutation of the retained assignment
list, with no source rewrite in the loaded design.
2. Prove a semantic refinement for the ordinary settle operation: iterating
   `settleRaw` to quiescence, or equivalently evaluating one topological
   permutation, is independent of the chosen topological permutation and
   equals the IEEE continuous-assignment fixpoint. The existing one-pass
   `topoC` theorem remains a fast path and a conservative profile predicate.

Only after those theorems exist should the tactic accept a non-`topoC` design.
The tactic may search for or consume a finite topological-order certificate,
but it must not silently sort the source AST or replace the semantics with a
second evaluator. A self-read or a real dependency cycle remains refused.
Dynamic names, unresolved widths, and memory reads whose dependency footprint
is not certified remain outside this proposal.

This is a trusted semantic change, not a route-local simp improvement. No
implementation is claimed by this proposal.
