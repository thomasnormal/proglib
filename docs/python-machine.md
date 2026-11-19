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

`RLabel.tau` is silent. Event labels carry returns, refusals, choices, and
raises. Resource points are represented by `RControl.resourceChoice`, which
has both a proceed transition and an ordinary transition into a raising
control state. An uncaught raising state produces the corresponding raise
event. The relation does not count fuel. `Step.choose` requires
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

`parseMachineModule` decodes the approved extractor envelope into this schema.
`compileMachineModule` is currently a small explicit frontier conversion for
the relation's admitted scalar and control nodes. Unsupported machine nodes
remain loud refusals until their relation cases land.

## Family order

Each family lands its node cases, differential rows, proof rules, and verified
deletion targets together. A machine row is counted only when the relation
decides it and agrees with CPython. A refusal is reported separately.

### B scopes, names, functions as values, and minimal objects

The current machine B resolver has a live `__main__` namespace, local-first then
module lookup, function values in that namespace, positional call-frame
dispatch, and caller resumption on return. Each `def` receives a stable
function-value token, so aliases continue to call the original object after
the defining name is rebound. Its checked row defines `read`, mutates a module
global, then calls `read` so the callee observes the new value. Keyword
arguments, defaults, and closures remain refusals until their own cases land.
Minimal classes with no decorators, keywords, or unsupported body statements
now retain mutable class attributes, including later assignments and deletion
through a class value. Plain methods without decorators or annotations are
also stored as callable class attributes. Instantiation creates an instance
with mutable attributes and class fallback. Single inheritance and direct
multiple inheritance resolve class attributes, methods, and `__init__` in
base-list order. Missing attributes raise `AttributeError`. Multiple
inheritance with inherited bases, cycles, and other class metadata remain
outside this slice. A leading string literal in a class body initializes
`__doc__`; other class metadata remains outside this slice. Static
Instances with an undecorated `__len__` method participate in `len()` through
the same bound-method call path; invalid `__len__` results remain refused.
`repr()` dispatches to an explicit instance `__repr__` method and accepts its
string result. Default object rendering remains refused.
`str()` dispatches to an explicit instance `__str__` method and accepts its
string result. Default instance string conversion remains refused.
`abs()` dispatches to an explicit instance `__abs__` method and accepts its
integer result. Unsupported absolute-value protocols remain refused.
Subscription on an instance dispatches to an explicit `__getitem__` method;
ordinary list and dictionary indexing continues through their existing paths.
Containment on an instance dispatches to an explicit `__contains__` method,
with the item passed before the container's bound receiver.
Unary negation on an instance dispatches to an explicit `__neg__` method;
integer unary negation keeps its existing path.
Unary plus on an instance dispatches to an explicit `__pos__` method;
integer unary plus keeps its existing path.
Addition with an instance on the left dispatches to an explicit `__add__`
method; integer and string addition keep their existing paths.
Subtraction with an instance on the left dispatches to an explicit `__sub__`
method; integer subtraction keeps its existing path.
Multiplication with an instance on the left dispatches to an explicit
`__mul__` method; integer multiplication keeps its existing path.
True division with an instance on the left dispatches to an explicit
`__truediv__` method. Scalar true division remains outside this relation
frontier.
Floor division with an instance on the left dispatches to an explicit
`__floordiv__` method. Scalar floor division keeps its existing frontier.
local-name tracking raises `UnboundLocalError` for a read or
delete before assignment. Rows cover globals, definition order, redefinition
identity, shadowing, nested calls, and defaults evaluated at definition time.
The current deletion candidates that exist are
`LeanModels/Python/Json.lean:parseFunctionDefn`,
`LeanModels/Python/Semantics.lean:findFunction`,
`LeanModels/Python/Semantics.lean:globalCallEnv`, and
`LeanModels/Python/Script.lean:scriptForwardName`. They remain until the
relation's corresponding scope and module cases replace them.

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

`Main.lean` exposes `--relation-script-batch` and runs the machine decoder and
relation frontier. The harnesses print
`MACHINE-REL scripts decided/169` and `MACHINE-REL cases decided/5033`, with
divergence counts, and fail on divergence or runner and unit expectation
errors. These are coverage measurements, not parity claims for refused rows.

## Specification boundary

The relation is intended to follow the Language Reference. CPython 3.9 is the
differential oracle and implementation record for choices such as identity,
allocation, set probing, resource outcomes, float rendering, and message
text. It does not define the relation.
