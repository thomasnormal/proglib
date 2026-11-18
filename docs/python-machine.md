# Python small-step machine design

This is the design contract for the Python semantics. The input is the
approved CPython 3.9 `ast` envelope. Lexing, parsing, and source text are
outside the boundary. The relation is defined on AST nodes in source order.
Ingestion does not hoist definitions, lower comprehensions, or attach census
flags to the nodes seen by the machine.

## Definition and runner

The machine configuration is a frame stack, continuation control, heap, module
namespace store, pending exception values, open choice points, and status. A
frame owns its lexical locals, globals reference, current statement or
expression continuation, and handler context. The machine has no fuel or
resource counter.

The semantic judgment is

```
Step : Config -> Label -> Config -> Prop
Trace : Config -> List Label -> Config -> Prop
```

`Label.tau` is silent. Event labels carry output, external calls, imports,
choices, raises, returns, or typed refusals. A resource raise is a normal
transition and leaves a catchable exception value in the configuration. A
`RecursionError` transition is allowed at every frame push. A `MemoryError`
transition is allowed at every allocation. Their class and structured args are
semantic data. Exception message text belongs to the implementation record.

`RImpl` resolves an explicit choice from its allowed token set and supplies
external results. `runRelation` repeatedly resolves one allowed transition.
It is outside the definition. `runRelation_trace` proves that every runner
trace is a `Trace`, and the proof uses the `Step` constructors rather than a
definitionally equal graph. `RImpl.cpython39` is the first implementation
record. It does not change the relation or its quantification over choices.

## Choice points and resources

The relation records choices for object identity and small-integer caching,
hashing and set/dict probing order, mutation during iteration where the
reference leaves an outcome open, finalizer timing, float rendering,
environment and import results, and implementation-defined accelerator
results. The allowed set is part of each `Choice` value, and a `Step.choose`
transition requires membership in that set.

The relation does not count CPython recursion units. Resource transitions are
permitted wherever a frame or object allocation occurs, and the resulting
exception can be handled by the ordinary handler continuations.

## AST and control rules

The machine's raw envelope mirrors the approved AST node shape. `RStmt` keeps
definition, class, import, assignment, loop, return, expression, and refusal
nodes in the statement list. `Expr` nodes remain expressions until their own
continuation runs. A node outside the current family is a typed refusal that
retains its kind, text, and span. The semantic relation never reads
`Module.functions`, `argsOk`, `localsOk`, or an ingestion census.

Expression evaluation uses continuation states. Literal evaluation is already
small-step, and returns and expression statements resume through a continuation
instead of calling a second evaluator. Calls, handlers, loops, iteration, and
`finally` blocks extend this same continuation stack in later families.

## Family landing order

Every family lands its node cases, rows, proof rules, and deletion targets in
one family commit. Acceptance rows are the named differential rows in the
machine and script corpora. A row is accepted only when the machine agrees
with CPython or refuses loudly. The existing old interpreters remain until the
machine decides every row they decide with zero divergence.

### I. Machine and program logic

Acceptance rows cover literal return, ordered expression continuation, output,
refusal, resource raise, and an allowed choice. The relation and trace
membership theorem are present. Deletion targets are
`LeanModels/Python/Semantics.lean:Run`,
`LeanModels/Python/Monadic/Eval.lean:Run`,
`LeanModels/Python/Obs.lean:adequacy`, and
`LeanModels/Python/PayloadBlind.lean:adequacy` after parity. Existing
examples depending on those judgments are re-proved over `Trace`.

### B. Scopes, names, function values, and minimal objects

Acceptance rows cover module-global reads, call-before-definition,
redefinition, shadowing, nested calls, and defaults evaluated at definition
time. The mechanism is one frame stack and a heap namespace. Deletion targets
are `LeanModels/Python/Json.lean:parseFunctionDefn`,
`LeanModels/Python/Script.lean:findFunction`,
`LeanModels/Python/Semantics.lean:globalCallEnv`, and
`LeanModels/Python/Semantics.lean:scriptForwardName`.

### H. Registry and argument binder

Acceptance rows cover positional, positional-only, defaults, `*args`,
keyword-only, `**kwargs`, duplicate arguments, missing arguments, and unknown
keywords. The binder consumes raw `ast.arguments` and returns a structured
`TypeError` on failure. Deletion targets are
`LeanModels/Python/Semantics.lean:mergeKwArgs`,
`LeanModels/Python/Monadic/Eval.lean:bindParams`,
`LeanModels/Python/Json.lean:argsOk`, and
`extractors/python/extract.py:literal_const_payload`.

### C. Iteration and generators

Acceptance rows cover iterator creation timing, list and dict mutation,
generator suspension, `yield from`, and comprehension scopes. Deletion targets
are `LeanModels/Python/Json.lean:lowerGeneratorExpr`,
`LeanModels/Python/Json.lean:lowerListComp`,
`LeanModels/Python/Semantics.lean:genInitCont`, and
`LeanModels/Python/Monadic/Eval.lean:stepIter`.

### E. Exceptions as objects

Acceptance rows cover class matching, handler order, re-raise, `finally`,
`with`, and catchable resource raises. Deletion targets are
`LeanModels/Python/Semantics.lean:exceptionTable`,
`LeanModels/Python/Semantics.lean:unwindException`, and
`LeanModels/Python/Monadic/Eval.lean:raiseFlow`.

### A. Full object model

Acceptance rows cover class creation, inheritance, descriptors, constructors,
bound methods, and callable protocol dispatch. Deletion targets are
`LeanModels/Python/Json.lean:classAdmission`,
`LeanModels/Python/Semantics.lean:literalDunder`, and
`LeanModels/Python/Semantics.lean:methodNameTable`.

### D. Containers and hashing

Acceptance rows cover aliases, mutation, views, hashing, set order, and
dictionary probing choices. Deletion targets are
`LeanModels/Python/Semantics.lean:heapPlus`,
`LeanModels/Python/Semantics.lean:containerSpecialCases`, and
`LeanModels/Python/Monadic/Eval.lean:dictCursor`.

### F. Modules

Acceptance rows cover ordered module initialization, imports, rollback, and
live namespace rebinding. Deletion targets are
`LeanModels/Python/Script.lean:initFoldLive`,
`LeanModels/Python/Script.lean:defsBoundBefore`, and
`LeanModels/Python/Semantics.lean:findFunction`.

### G. Numbers and strings

Acceptance rows cover integer, float, string, formatting, overflow, and exact
exception-class behavior. Deletion targets are
`LeanModels/Python/Semantics.lean:evalBinOp`,
`LeanModels/Python/Monadic/Eval.lean:evalNumeric`, and
`LeanModels/Python/Float64.lean:Float64` once the shared SoftFloat registry
exists.

### J. Instruments and parity

Acceptance rows cover every existing script-corpus row and every decided
`cases.json` row. The instrument prints the pinned oracle version, compares
exception class and stdout text, and reports
`MACHINE-PARITY decided/decided, diverging 0` separately from unit rows.
Deletion targets are `harness/machine_diff.py:machineRows`,
`harness/script_corpus.py:machine_script_batch`, and the compatibility runner
entry points in `Main.lean` after the switch.

## Two interpreters: cost of each deletion

The relation is the replacement point for both old control layers. Deleting
`Semantics.lean:Run` requires re-proving scalar expression and statement
lemmas over `Step`. Deleting `Monadic/Eval.lean:Run` requires re-proving heap,
generator, and exception rows over the same transition relation. Deleting
`Obs.lean` and `PayloadBlind.lean` removes the 292 adequacy bridges and their
example imports. The three-proof pilot is a literal return, a heap mutation,
and a caught exception. Each pilot must use the user judgment and retain only
the standard Lean axioms.

## Where the specification copies CPython

The machine follows the Language Reference. It records CPython 3.9 only in the
implementation record for small-integer identity, object allocation choices,
set probing order, recursion and memory outcomes, float rendering, and
exception message text. Differential rows exercise those implementation
records. They do not define the relation.

## Current implementation

The relational kernel is `LeanModels/Python/Machine/Relation.lean`. The old
compatibility runner remains in `LeanModels/Python/Machine/Core.lean` while
the family steps land. The kernel has no fuel or budget in `RConfig`, uses
silent and event labels, exposes explicit allowed choices, and includes
nonterminal resource-raise transitions.
