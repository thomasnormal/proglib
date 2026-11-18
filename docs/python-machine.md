# Python small-step machine design

The machine work is an additive prototype over structured AST data. Source
parsing remains outside the semantics boundary. The compatibility `Module`
interpreter and its runner are still present while the relational machine is
built.

## Current relational kernel

`LeanModels/Python/Machine/Relation.lean` defines `Step`, `RTrace`, a
fuel-free `RConfig`, and a derived resolver. The configuration has frames,
heap, open choices, the selected choice token, and a status. A frame carries
control, locals, and globals. `RControl` includes statement lists,
expression continuations, sequencing and assignment continuations, and a
raising state.

`Label.tau` is silent. Event labels carry returns, refusals, choices, and
raises. Resource raises are ordinary transitions into a raising control state.
An uncaught raising state produces the corresponding raise event. The
relation does not count fuel or store a resource point. `Step.choose` requires
the token to belong to the choice's allowed set and records that token in its
successor.

The B1 kernel check runs a sequence containing a docstring expression, two
assignments, a binary expression, and a final name expression to normal module
completion. The B2 kernel check exhibits distinct recursion and memory raise
successors from one reachable configuration.

## Machine-only envelope

`LeanModels/Python/Machine/Ingest.lean` contains the machine-facing schema.
`MExpr`, `MStmt`, `MArguments`, aliases, handlers, with-items, and modules
retain AST fields such as target arrays, optional slice bounds, decorators,
keyword arguments, `Global`, `Nonlocal`, `For`, `AugAssign`, `Delete`,
`Try`, `With`, `Raise`, `Break`, and `Continue`. Joined strings,
formatted values, and comprehensions remain explicit nodes. This schema does
not call `Json.lean`, perform a census, or lower a node.

The decoder from the approved extractor envelope into this schema is the next
machine task. Until it lands, the relation batch entry point reports a loud
frontier refusal for compatibility envelopes.

## Family order

Each family lands its node cases, differential rows, proof rules, and verified
deletion targets together. A machine row is counted only when the relation
decides it and agrees with CPython. A refusal is reported separately.

### B scopes, names, functions as values, and minimal objects

Rows cover globals, definition order, redefinition, shadowing, nested calls,
and defaults evaluated at definition time. Planned deletion targets are
`LeanModels/Python/Json.lean:parseFunctionDefn`,
`LeanModels/Python/Script.lean:findFunction`, and
`LeanModels/Python/Semantics.lean:globalCallEnv`. `scriptForwardName` is in
`LeanModels/Python/Script.lean` and remains until the machine module system
replaces it.

### H registry and argument binder

Rows cover positional, positional-only, defaults, varargs, keyword-only,
kwargs, duplicate arguments, missing arguments, and unknown keywords. The
raw `MArguments` fields are the machine input. Existing binder code remains
until the machine handles these rows.

### C iteration and generators

Rows cover iterator creation, mutation during iteration, suspension,
`yield from`, and comprehension scopes. The machine schema retains generator
and comprehension nodes. Existing lowering remains until relation parity.

### E exceptions as objects

Rows cover handler matching, re-raise, `finally`, `with`, and catchable
resource raises. Exception class and structured arguments are semantic data.
Message text belongs to the implementation record.

### A, D, F, G, and J

The full object model, containers and hashing, modules, numbers and strings,
and the parity instruments follow the same family rule. Their deletion lists
will name declarations that exist when each family lands. No deletion target
is claimed for an absent symbol.

## Harness status

`Main.lean` exposes `--relation-script-batch`. It currently emits structured
refusals until the machine envelope decoder is connected. The harnesses print
`MACHINE-REL scripts decided/166` and `MACHINE-REL cases decided/5033`, with
divergence counts, and fail on divergence or runner and unit expectation
errors. These are coverage measurements, not parity claims for refused rows.

## Specification boundary

The relation is intended to follow the Language Reference. CPython 3.9 is the
differential oracle and implementation record for choices such as identity,
allocation, set probing, resource outcomes, float rendering, and message
text. It does not define the relation.
