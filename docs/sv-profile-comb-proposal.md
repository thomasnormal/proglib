# `always_comb` clocked-profile proposal

Status: proposal only; the current `seqOblI`/`seqOblB` predicates and `step_seqI`/`step_seq` theorems remain unchanged.

## Scope

The source-shaped executor already admits parser-native `always_comb` bodies through `CoreMemProc.comb`,
`runCombAt`, `runCombQuiesce`, and `runCombSettleQuiesce`.  The clocked profile currently rejects them indirectly
through `!E.hasComb` in `seqOblI` and `seqOblIM`.  The proposed profile must retain the exact active-region route:
continuous assignments and `always_comb` execute in the source-shaped active region, with the route's existing
quiescence refusal preserved when the executor limit is exhausted.

The proposal does **not** lower an `always_comb` body to a continuous assignment, choose an active-region order, or
turn a timeout into a value.  A body that is not converted, does not satisfy the existing `CombProcOkI` shape, has a
self/read-before-write hazard, or fails to settle remains refused.

## Trusted definitions

Add a comb-aware obligation predicate beside (not replacing) `seqOblI` and `seqOblIM`:

```lean
def CoreMemDesign.seqOblIC (E : CoreMemDesign) : Bool :=
  E.oblDrivers && E.topoC && E.oblInputsUndriven && E.oblSources &&
    E.oblNoSourceRead && E.oblEdgeOrder && E.oblConverted && E.oblComb
```

`oblComb` is source-shaped and parser-derived.  It accepts a `.comb body` only when the existing
`combProcOkIB body` certificate holds, rejects `.latch` (until its own semantics is admitted), and is true for the
edge/continuous-assignment forms already covered by the profile.  It must not be a test that merely checks
`hasComb`; a design with an unconverted or unsafe body must remain a loud refusal.

The memory-aware variant is the same replacement of `oblEdgeOrder` with `oblEdgeOrderMemory`:

```lean
def CoreMemDesign.seqOblIMC (E : CoreMemDesign) : Bool :=
  E.oblDrivers && E.topoC && E.oblInputsUndriven && E.oblSources &&
    E.oblNoSourceRead && E.oblEdgeOrderMemory && E.oblConverted && E.oblComb
```

Keep the old predicates as conservative compatibility profiles.  The old theorem must be proved in the new layer:
`seqOblI = true -> seqOblIC = true` when `E.hasComb = false`, and likewise for `seqOblIM`.

## Required semantic lemmas

The trusted change needs the following named, hand-usable lemmas before a tactic wrapper is added:

1. `oblComb_spec`: every successful `oblComb` decision yields the parser-native `CombProcOkI` receipt for each
   combinational process and excludes latches/unsupported processes.
2. `runCombSettleQuiesce_coherent_of_each`: from every coherent state, every successful arbitrary-limit combined
   active-region run preserves `Coherent` and `MemCoherent`.  The current branch has this receipt in
   `LeanModels/Sv/SeqCycleObl.lean`; its settle-totality premise is intentionally explicit.
3. A view/state bridge for the same run: a successful source-shaped view run and the retained-state run agree on the
   projected scalar view under `matV` premises.  This is required before defining a view-level comb slot theorem;
   the coherence-only receipt is not enough.
4. `slotCombV`: the view-level slot corresponding exactly to `prepareStep`/`edgePass` with the active-region comb
   runner before and after the edge.  It must preserve the existing memory queue and NBA commit equations.
5. `step_seqIC` and `step_seqIMC`: global, unbounded-in-time refinement theorems from `slotCombV` to `step`, with
   no tool-fuel premise in the statement.  The executor's `4096` remains only an internal loud-refusal guard.
6. `initialState_comb` and a comb-aware `cycle`/run bridge: time-zero active-region execution must be included, not
   silently replaced by the continuous-assignment-only initial state.

The existing `step_of_onePass_comb` theorem is the final route bridge once the two exact `prepareStep` and `edgePass`
receipts are supplied; it must not be used to hide a missing view/state correspondence.

## Conservativity and acceptance

Before changing the profile gate, prove that a design with no `.comb` process has exactly the old `seqOblI` result,
old `slotV`, and old `step_seqI` theorem.  Add differential rows for:

- a single scalar `always_comb` copy;
- a two-process comb chain, including out-of-source-order scheduling;
- conditional and case/default bodies;
- x/z on each input and intermediate signal;
- a negative row for a self-read/read-before-write body;
- a negative row for `always_latch`, an unconverted statement, and a quiescence refusal.

The final gate additionally requires one real module with `always_comb` proved both through the tactic and by hand from
the published lemmas.  Until those rows, the view/state bridge, and that worked proof exist, the marker remains
`PROFILE-COMB` open.
