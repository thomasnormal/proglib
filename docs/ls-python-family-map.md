# Python feature-family map

This map is the architecture plan for the current Python survey. It replaces
wall-by-wall ordering. The measurements below are from the CPython 3.9.25
stdlib sweep (166 files: 7 MATCH and 159 REFUSE, with no timeout, extract,
oracle, hung, or runner failures) and the 183-module manifest survey (4,095
MATCH, 4,533 REFUSED, 41 UNCOMPARABLE, one TIMEOUT, and seven unfinished
RUNNER rows). A survey row has one observed first wall, so the counts below are
presence counts, not causal flip promises. The JSON artifacts retain the full
file lists and every failing row.

The owner-selected build order is: (1) small-step machine and program logic,
(2) scopes/names/functions as values with a minimal object core, (3) the
external registry, (4) iteration, (5) exceptions as objects, (6) the full
object model, (7) containers, (8) modules, and (9) numbers on shared
SoftFloat. The sections below use that order; the current survey families are
mapped into it rather than treated as independent wall priorities.

## 1. Small-step machine and program logic

**Members.** Every admitted and refused construct depends on this control
kernel; the current generator frames are the clearest existing small-step
island. The target is one transition system with labelled events and explicit
choice points, with the runner derived from it.

**One mechanism.** A small-step machine over the approved CPython AST
envelope, frame stack, continuations, heap, event trace, and choice record;
program logic rules reason about its transitions.

**Today.** `Runtime.lean` has `Run`, `RFlow`, worlds, and generator frames;
`Semantics.lean` and `Monadic/Eval.lean` are deterministic big-step control
layers; `Obs.lean`/`PayloadBlind.lean` are fuel proof bundles.

**Missing and debt.** There is no event trace or choice parameter, and the
two control layers duplicate the transition work. Their fuel knots, generator
island, and proof-specific adequacy bridges are debt to replace with the one
machine. The approved CPython AST remains the theorem input by owner decision;
source text, lexing, and parsing are outside this theorem boundary.

## 2. Scopes, names, functions, and minimal object core

**Members.** Class creation is present in 102 stdlib files and is the first
wall in 63 manifest modules. Lambda/first-class callable forms occur in the
stdlib static inventory (80 Lambda nodes); class bases, decorators, metaclass
keywords, and unsupported class-body statements are the common refusal detail.

**One mechanism.** A runtime type object with ordered class-body execution,
method descriptor binding, instance layout, and one callable protocol for
functions, closures, methods, and class constructors.

**Today.** `Runtime.lean` has `ClassObj`, `InstanceObj`, `callClosure`, and
class construction; `Semantics.lean` and `Monadic/Eval.lean` each have their
own admission checks. `LeanModels/Python/Surface.lean` and the VC layer expose
calls but not a common callable object.

**Missing and debt.** The class-creation guard, `Lambda` refusal, closure
recursion guards, constructor special cases, and method-call adapters are debt
that the callable/type protocol should replace. This family depends on module
binding, object layout, and exception unwinding. The measured class wall has
62 modules, 2,015 driven calls, and 183 matching calls, but zero causal
function flips; those are observations, not the work order.

## 3. Library functions and accelerator boundaries

**Members.** `ImportFrom:accelerator-outside-domain` occurs in `bisect.py`,
`opcode.py`, and `stat.py`; `ImportFrom:accelerator-unmeasured` occurs in
`decimal.py`. The manifest has two accelerator-outside rows, one
accelerator-unmeasured row, and six currently verified public-function
modules in the class-wall slice. The runner's 123-row observer difference is
also part of this boundary.

**One mechanism.** A version-pinned external specification registry: each
permitted library function has a typed contract, CPython provenance, and a
single implementation/refinement boundary shared by the trunk and monadic
runner. Unregistered C behavior refuses loudly.

**Today.** `Monadic/Spec.lean` contains two mvcgen gates; `Main.lean`,
`tools/leanpy`, and the library survey drive external calls; no general
registry feeds the trunk proof surface.

**Missing and debt.** Accelerator refusal strings, builtin-specific tables,
runner-only admissions, and concrete vendored witnesses are special cases.
They should become registry entries with differential rows and, where useful,
proofs. This family depends on module loading, object layout, numeric
semantics, and callable protocols. Its joint MATCH count is intentionally
unclaimed: a body can match while an accelerator call remains partial.

## 4. Iterators, generators, and comprehensions

**Members.** The stdlib static inventory contains Set display (63 nodes),
Delete (21), YieldFrom (32), ListComp (10), SetComp (8), Starred display (7),
Dict unpack (6), GeneratorExp (3), and DictComp (2). The live manifest also
contains the admitted one-clause DictComp boundary and refusals for filtered or
multi-clause forms.

**One mechanism.** A first-class iterator cursor over a heap object, with
ordered target assignment, fresh comprehension scope, mutation-visible state,
and explicit `StopIteration`/exception flow. Comprehensions and unpacking
should be consumers of this cursor, not separate lowerings.

**Today.** `Semantics.lean` has `rangeVals`, `execFor`, generator steppers,
heap list/dict workers, and the one-clause `evalDictComp` arm. The monadic side
has `Kont` cursors and a direct DictComp stepper. `Obs.lean` and
`PayloadBlind.lean` carry selected fuel/world lemmas.

**Missing and debt.** `YieldFrom`, generator delegation, live dictionary
iteration, starred display, deletion, set construction, and filtered/multi-
clause DictComp each have special-case gates. They should be replaced by the
cursor plus scope protocol. This family depends on object layout, callable
protocols, and exception flow. The survey records the static members above;
there is no valid joint MATCH count until those dependencies are implemented
and differentially exercised.

## 5. Exceptions and structured control flow

**Members.** The stdlib sweep has one first-wall `try/except` row
(`_compat_pickle.py`, an `else` clause); manifest rows also include partial
handler, `finally`, generator, and call-unwind cases.

**One mechanism.** A single structured flow result carrying normal, return,
break, continue, and raised-exception outcomes, with handler matching and
world/frame retention specified once.

**Today.** `Runtime.lean` defines `Run` and `RFlow`; `Semantics.lean` has
`execTry`/statement execution; `Monadic/Eval.lean` has `Res`, `Kont`, and
`finishCallM`. The VC2 work records stateful call unwinding but the top-level
heapful bridge remains incomplete.

**Missing and debt.** The `try/except else` refusal, several-handler and
finally gates, exception-class construction adapters, and duplicated call
unwind transport are special cases. Replace them with one flow/handler
machine. This family depends on callable/class protocols and object layout;
its only direct stdlib first-wall count is one, while its dependency surface
is spread through the manifest's partial rows.

## 6. Full object model: memory and layout

**Members.** The heap `+` wall (`__future__.py`), list `.extend`
(`unittest.py`), missing `frozenset` (`keyword.py`), missing `globals`
(`token.py`), and the manifest's heap-backed container partial rows.

**One mechanism.** A typed heap object layout with a single protocol table for
allocation, lookup, mutation, iteration, and builtins. Operations take an
explicit world and return a classified result; no builtin-specific fake value
is permitted.

**Today.** The trunk heap model is in `LeanModels/Python/Runtime.lean` and
`Semantics.lean` (`Heap`, `heapGet`, `heapSet`, `heapAppend`, `heapPop`,
dict/set workers). The monadic evaluator mirrors these in
`LeanModels/Python/Monadic/Eval.lean`.

**Missing and debt.** There is no common layout for all container protocols,
so `heap-plus`, `.extend`, `frozenset`, and `globals` are separate refusal
leaves. The builtin arms and concrete heap witnesses are debt to replace with
the one table. This family depends on module/name resolution and callable
argument binding before a heap operation can be reached. The survey contains
five named first-wall files and additional partial manifest modules; no joint
flip count is claimed until those dependencies are run together.

## 7. Containers and views

**Members.** Lists, dictionaries, sets, views, tuple/list displays, deletion,
unpacking, and the heap-plus/extend/frozenset walls named in family 6.

**One mechanism.** One abstract container protocol over the object layout and
iterator cursor, with mutation, hashing, equality, view liveness, and order
choices explicit in the implementation record.

**Today.** `Runtime.lean` stores list/dict/set/view objects; `Semantics.lean`
and `Monadic/Eval.lean` have separate heap workers and method switches.

**Missing and debt.** `heap-plus`, `.extend`, `frozenset`, set-order tables,
view-specific gates, and synthetic `<dictkeys>`/delete builtins are special
cases. The container protocol deletes those admission checks and ingestion
rewrites once it exists. It depends on families 1, 2, 4, and 6.

## 8. Modules, loading, and name binding

**Members.** `Import` is present in 150 stdlib files (807 static nodes),
`ImportFrom` in 239 nodes, and definition-order is the first wall in 34
manifest modules. The manifest examples include `_aix_support`, `base64`,
`copyreg`, `email.parser`, `heapq`, and `linecache`; the exact list is in the
survey artifact. Accelerator imports (`bisect.py`, `opcode.py`, `stat.py`,
and `decimal.py`) are the external-boundary subfamily below.

**One mechanism.** Ordered module loading with an explicit module namespace,
export table, import cache, and source-order function/class binding. Resolution
must distinguish a live local, a module global, a builtin, and an absent name.

**Today.** `ModuleInit.lean`, `Semantics.lean` (`moduleGlobals`, `evalOpen`,
`findFunction`), and `Monadic/Eval.lean` implement separate pieces. The
protocol census records shared `lookupG` but not one complete resolver.

**Missing and debt.** `Import`/`ImportFrom` refusal branches, the
position-independent function table, and the unresolved combined local/global
resolver are special cases. They should be replaced by the ordered module
loader. This family depends on object layout (module objects and import cache),
external-library declarations, and class construction. The current survey
has 48 stdlib files whose first observed wall is import and 34 manifest files
whose body reaches definition-order; the number that becomes MATCH only after
all four dependencies is not measured and must not be inferred from `sole`.

## 9. Numeric and floating-point semantics

**Members.** The direct stdlib heap-binary-plus refusal is `__future__.py`;
manifest rows also contain float, power, conversion, and mixed numeric partial
calls. Numeric rows that need C accelerators remain external boundaries.

**One mechanism.** A typed numeric tower with exact integer operations and the
pinned binary64 bit-level operations, returning the same classified overflow,
zero-division, and non-finite outcomes in both interpreters.

**Today.** `Float64.lean`, `Semantics.lean` numeric workers, and
`Monadic/Eval.lean`'s `binOpM`/conversion arms provide separate scalar paths;
`Examples/python/float_lab` records exact-bit witnesses.

**Missing and debt.** Heap numeric dispatch, mixed int/float ordering, power
edge cases, and platform-dependent library math are special-case arms. They
should be replaced by the numeric tower plus explicit external declarations.
This family depends on object layout and callable protocol; no causal family
flip is claimed by the current survey.

## 4. Two interpreters: deletion cost

The current trunk interpreter is `LeanModels/Python/Semantics.lean` (12,351
lines). It is used by `Surface.lean`, `Obs.lean`, `VC.lean`, `VC2.lean`,
`VCGen.lean`, `VCTactic.lean`, `LoopTactic.lean`, `Delab.lean`, the proof
examples, and the public `CallsTo`/`PartialTo`/`Raises` judgments. There are
37 Python `proof.lean` files with 245 theorem/lemma declarations. Deleting
this interpreter would require redefining those judgments over the monadic
runner, then re-proving every proof tactic and every example theorem; the
current `py_prove`, `py_begin`, `py_loop`, `py_vcgen`, and `py_corollary` stack
has no monadic counterpart. The only monadic proof route today is
`LeanModels/Python/Monadic/Spec.lean` (338 lines, two rebuilt gates).

The monadic evaluator is `LeanModels/Python/Monadic/Eval.lean` (12,762 lines),
with `Monadic/Script.lean`, `Main.lean`, `tools/leanpy`, the differential
runner, and both survey harnesses depending on it. Deleting it would lose the
fuel-free `PyM`/`callInM` execution, script/world observations, the executable
runner, and the mvcgen route. The trunk would need a stateful script runner,
world observations, and a replacement proof-triple layer before those users
could return. The 123-row observer difference in the ledger is therefore a
real migration surface, not a theorem that can be erased.

The three-proof pilot is deliberately small and honest: the straight-line
`Examples/python/add` check reduces under the monadic route; the loop
`Examples/python/tri` proof and the stateful `list_lab.bump_twice` proof do not
close by kernel reduction, so no monadic loop or `CallsIn` port is claimed.
Before/after line counts are the measured counts above; no proof timing is
invented for pilots that did not typecheck. The remaining cost is to re-prove
the public surface, all loop and call rules, the 37 example files, and the
runner's differential contract if either interpreter is removed.

The independent architecture review and ROADMAP section 9 draft support this
direction, with two corrections from the current tree. I confirm that a future
definition should be one small-step machine with labelled events and explicit
choice points, with the runner derived from it; I have not started that machine
because it is an owner decision. I also confirm that scope, object layout,
callable dispatch, iterators, exceptions, and external specifications are the
right build families. I correct the review's proof-file and declaration counts
with the current checkout above, and leave its larger ten-family breakdown as a
refinement of this nine-family map rather than claiming that its estimated
machine size has been measured. **OBJECTION module system:** the review's
description of `initFoldLive` continuing after a failed top-level statement is
a current semantic debt and a likely wrong answer, not a behavior the new
definition may preserve. The approved CPython AST is the theorem input by
owner decision; source text, lexing, and parsing are outside the theorem.

### WHERE THE SPEC COPIES CPYTHON

These are implementation choices currently embedded in the semantics and must
move behind an explicit CPython implementation record. They are not clauses of
the Python language definition:

- the small-integer identity cache used by `is`;
- the set hash-table layout and probing sequence used to produce iteration
  order;
- C-level recursion units and the limit of 1000;
- exception message text tables, including exact punctuation;
- binary64 float rendering digits and other repr formatting details;
- the closed-function module initializer's poisoning/live-view behavior,
  including continuing after a failed top-level statement;
- accelerator availability and the choice of CPython's concrete external
  library implementation;
- identity and hash choices for immutable objects, dict/set order, and the
  resolution of resource exhaustion.

Rows already waiting for these implementation-defined choices include
`dict_lab.distinct_literals` and `dict_lab.self_cycle_eq` (identity and
recursion), `set_lab.sorted_set` and the set membership rows (set order and
hash probing), and the explicit recursion pools in
`harness/recursive_entry_probe.py`, `harness/recursion_limit_probe.py`, and
`harness/foundation_edges.py`. They are differential evidence, not definitions
of the choices; the future machine will check that CPython's selected
resolution belongs to the allowed set.

The Language Reference and library documentation remain the specification. The
CPython 3.9 oracle supplies tests and later representation-refinement evidence;
it does not define these choices. The future machine must quantify over choices
the language leaves open and carry CPython selections only through its explicit
implementation record.

## Architectural decision

If starting today, I would keep one approved AST envelope and one small-step
state/flow semantics with events and explicit choice points,
then derive both the executable runner and the proof surface from it. The
current trunk `Semantics.lean` and monadic `Eval.lean` duplicate dispatch,
recursion checks, heap protocols, and error ordering; the deletion-cost ledger
records the measured impact. The VC surface also pays a new bridge per
construct because it targets the trunk's fuel interpreter, while
`Monadic/Spec.lean` has only two mvcgen gates. Special-case tables for imports,
class creation, generators, and accelerator calls hide the missing protocol
boundaries. The replacement architecture is: one parser envelope; one
world/frame/flow machine; one object/callable/iterator protocol registry; a
fuel adapter for proofs; and a separate, explicit external-spec registry.
Until that consolidation is designed and proved, no new one-off survey wall
should be started. This is a plan recorded for the owner, not an implementation
request; the machine remains frozen until the inbox says `MACHINE: GO`.
