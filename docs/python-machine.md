# Python small-step machine design

This document records the machine approved by the owner on 2026-11-17. It is a
 design contract, not an implementation. The machine is the one Python
semantics; the existing trunk and monadic evaluators are frozen compatibility
artifacts until machine parity permits their deletion. The theorem input is the
approved CPython 3.9 `ast` envelope. Source text, lexing, tokenization, and
parsing are outside this boundary.

## Definition and derived runner

A configuration is a tuple

```
MachineState = {
  frames       : List Frame,
  continuations: List KontFrame,
  heap         : Heap,
  modules      : ModuleStore,
  events       : List Event,
  choices      : ChoiceTrace,
  resources    : ResourceState
}
```

A `Frame` contains the current AST statement/expression position, lexical scope
slots, the function result slot, and the handler context. A `KontFrame` records
the continuation needed after an expression, call, iterator step, handler, or
finally block. The heap stores abstract Python objects and references; its
representation does not expose CPython reference counts or object layout.
`modules` contains ordered module namespaces and import state. `resources`
contains abstract exhaustion conditions; it is not a CPython recursion counter.

The definition is a labelled transition relation

```
step : MachineState -> Event -> MachineState -> Prop
```

and its finite/infinite trace closure `steps`. A normal return, Python
exception, refusal, and resource exhaustion are terminal observations of the
closure. A theorem is stated as reachability or trace inclusion over this
relation. `CallsTo`, `CallsIn`, `PartialTo`, and `Raises` become derived
projections of machine reachability; they do not define a second evaluator.

The executable runner is derived, not primitive. An implementation record
`Impl` supplies a resolution for each permitted open choice and a registry for
external operations. `run Impl fuel ast input` repeatedly chooses a transition
allowed by `step`, records its event, and stops at the selected resource bound.
The first implementation record is `Impl.cpython39`; it explains CPython's
choice while remaining separate from the definition. The foundational theorem
is `run Impl.cpython39 ... ∈ steps ...`: every runner result is a behavior the
relation permits. The relation itself never calls CPython or selects a favorite
resolution.

## Events and external boundaries

Events are structured values, not formatted stdout strings:

- `output(text)` for writes to the program's output stream;
- `external(name, args, result)` for registry calls such as `time`, files,
  environment, and C accelerators;
- `importBegin(name)` and `importEnd(name, outcome)` for module boundaries;
- `choice(kind, token)` for an explicit open-language choice;
- `raise(class, args)` and `return(value)` for observable terminal flow;
- `resource(kind)` for an allowed `RecursionError`/`MemoryError` outcome.

The registry gives every external a typed contract, an abstract result set, and
provenance. A CPython implementation record may resolve it to one result, but
the specification quantifies over every result admitted by the contract.
Exception class and structured arguments are part of the definition. Exception
message text is implementation-defined and belongs to `Impl`; CPython 3.9's
text is tested separately. Output and external-call events remain visible in
the trace even when a convenience `CallsTo` projection ignores them.

## Choice points and resources

The relation leaves these choices explicit where the language or platform does:

- identity of immutable objects and the small-integer cache;
- hash values and set/dict probing and iteration order;
- dictionary/set mutation during iteration when the reference permits more than
  one outcome;
- finalizer timing and external environment results;
- float rendering choices that are only constrained by round-tripping;
- import registry results and implementation-defined accelerator behavior;
- resource exhaustion at frame pushes, allocations, or other bounded operations.

`RecursionError` and `MemoryError` are always permitted resource outcomes. The
specification never counts CPython's C recursion units and never promises a
value after resources are exhausted. The runner's numerical limits live in
`Impl.cpython39`. A correctness theorem therefore reads “returns the specified
result unless an allowed resource outcome occurs.”

## AST and control rules

Each AST constructor gets its own transition cases. The machine does not lower a
comprehension into a function, turn `del` into a synthetic call, or replace a
class with a table before semantics sees it. Scope analysis, function/class
objects, calls, iteration, exceptions, and module statements are transitions
on their original nodes. A construct outside the current family is a typed
refusal transition, retaining its node kind and location. No refusal is a
normal return and no unsupported construct is silently skipped.

The machine uses continuation frames for calls, loops, iterators, handlers,
`finally`, and `with`. A generator is an ordinary suspended machine state with
its continuation stack; it is not a second evaluator. A call pushes a frame and
passes the shared heap and module store. A return or exception unwinds the
continuation stack while retaining the events and permitted world effects.

## Family landing order and deletion targets

The owner-selected order is the following. Each family is complete only when
its AST cases, machine transitions, differential rows, derived proof rules, and
listed deletion targets are handled.

1. **Machine and program logic.** Add `step`, traces, choices, resources, and a
   weakest-precondition/reachability judgment. Delete the duplicated mutual
   fuel knots, the generator-only island, and the two interpreter control
   layers only after parity.
2. **Scopes, names, functions as values, minimal objects.** Replace static
   poisoning/live-fold rules, closure snapshots, `<cell>` encodings, lambda and
   definition-order censuses, and position-independent function tables.
3. **One external registry and argument binder.** Replace builtin if-chains,
   synthetic builtin names, accelerator allowlists, and ad-hoc keyword binders.
4. **Iteration and generators.** Replace per-construct cursor switches,
   generator delegation gates, comprehension shape gates, and ingestion
   lowerings with iterator/continuation transitions.
5. **Exceptions as objects.** Replace flat exception tables, one-handler
   restrictions, duplicated unwind transport, and special `with` guards with
   object/class matching and handler/finally continuations.
6. **Full object model.** Replace class-creation guards, literal-dunder
   recognizers, constructor switches, and method-name tables with type objects,
   descriptors, MRO, and callable protocols.
7. **Containers and hashing.** Replace heap-plus/extend/frozenset refusals,
   set-order special cases, view gates, and synthetic delete/dict-key calls with
   one abstract container protocol and explicit choices.
8. **Modules.** Replace `initFoldLive` rollback/poisoning, definition-order
   script gates, import tables, and module-global special cases with ordered
   namespace and import transitions.
9. **Numbers and strings on shared SoftFloat.** Replace duplicate numeric
   dispatch and the separate `Float64.lean` arithmetic path with the shared
   numeric registry and implementation parameters.

The differential harness gains a third mode from the first machine commit:
`MACHINE-PARITY n/4968, diverging k`. A refusal is acceptable; a decided
machine/CPython mismatch is not. The runner switches only after every row the
current runner decides is machine-decided with zero divergence. At that point
and in the same deletion series, the old control layers and their adequacy
proofs are removed. Existing theorem statements are re-founded over the
machine; the 292 monadic adequacy bridges are not ported.

## Acceptance gates for the first machine slice

The first slice covers literals, ordered scalar expression evaluation,
assignments, returns, `if`, `while`, and the terminal flow classes. Calls and
container iteration remain typed refusal transitions until their families land.
It provides:

- a kernel-reducible `step` and trace closure;
- an `Impl.cpython39` choice resolver and the runner-membership theorem;
- trace rows for output, return, exception, refusal, and resource exhaustion;
- machine-vs-CPython differential comparison with zero decided divergence;
- a toy trace-refinement theorem and a program-logic rule for one straight-line
  function;
- no edits to the frozen old interpreters except compatibility wiring required
  to build the machine runner.

The implementation is in `LeanModels/Python/Machine/Core.lean`. The derived
script runner is available through `leanmodels-run --machine-script-batch`.
`harness/machine_diff.py` runs the first real rows through CPython and the
machine in one batch. `harness/scripts/hello.py` and
`harness/scripts/scalar_expr.py` are matching scalar-output rows, and
`harness/scripts/function_call.py` checks a positional module-function call,
`harness/scripts/function_print.py` checks a direct-return call inside
`print`, and `harness/scripts/function_branch.py` checks branch selection in a
function body, while
`harness/scripts/cpython_list_basics.py` checks the explicit list refusal. The
current result is five matches, one refusal, and zero divergence.
