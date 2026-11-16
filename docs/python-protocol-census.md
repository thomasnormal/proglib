# Python protocol census

Foundation step 2 (2026-11-10), refreshed 2026-11-11. This is a source
census, not a refinement claim. The CPython column names the entry point and
the protocol calls that can observe an argument. The two Lean columns name the
worker reached by each surface. `shared` means both surfaces call the same
worker; `separate` marks a control or transport wrapper that still needs an
adequacy theorem.

The F9 ledger also has a concrete assignment-body bridge:
`Monadic.finishCallM_assign_constant_body_ok` runs a name assignment through
the fuel-free statement walker and the stateful call restoration boundary. It
is theorem-only and leaves the assignment AST shape intact; general assignment
expressions and recursive calls remain open.

The matching exception path is covered by `Monadic.leaveCallM_modify_exn`,
using the generic `toRun_tryCatch_exn` substrate equation. A raised Python
error retains the mutated world and receives the same nested-frame depth
decrement as a successful return.

The top-level restoration half is now symmetric: `Monadic.finishCallM_modify_exn`
proves that an exception after an arbitrary world mutation restores the
requested boundary depth while retaining the mutated world.

## Protocol families

| CPython 3.9 entry and call order | Trunk (`Semantics.lean`) | Runner (`Monadic/`) | Current observation / gap |
|---|---|---|---|
| `Objects/object.c:PyObject_RichCompareBool` (identity shortcut, then rich comparison) and `PyObject_RichCompare` | `valEq`/`valEqList` for ref-free values; `heapEq`/`heapEqList`/`heapEqEntries` for heap values; `keyEq`/`keyEqList` for hash-key probes; `heapContainsScan`; `rvalLt`/`rvalLtList` for ordering | `evalCompareOpH`, `valContains`, and the same workers through `Monadic.Prim` | **Closed for the admitted overlap:** `keyEq_bool_int_richCompare` proves `keyEq` and `valEq` agree on bool/int keys, and `richcompare_bool.py` drives scalar equality, list membership, dict probes, and nested equality in both interpreters. The remaining workers stay separate because CPython dispatches table lookup, container equality, and ordering through different protocol functions; non-finite identity remains a loud boundary. |
| `Objects/object.c:PyObject_IsTrue` (type `nb_bool`, then `sq_length`, then default true) | `truthyH` and `truthy` | `truthyM` → `truthyH` | shared; instances and generators use the admitted default protocol, while unsupported cells refuse. |
| `Objects/object.c:PyObject_Hash` and `Objects/dictobject.c` key lookup (hash, then equality) | `hashableKey`, `setHashNat`, `dictFind`/`keyEq`, dict/set key gates | same workers through `liftRes` and evaluator arms | **Closed for the admitted key domain:** `keyEq_false_of_unhashable_left` and `dictFind_unhashable` prove the hash gate prevents an unhashable probe from matching; `hashkey_probe.py` covers bool/int collisions, tuple keys, and the unhashable TypeError in both interpreters. Hashing and equality remain separate CPython protocols; identity hashes and unsupported set construction refuse. |
| `Objects/abstract.c:PyNumber_Index`, then `PyNumber_AsSsize_t` / `Objects/listobject.c` Clinic conversion | `asInt`, `asRangeBound`, then `pySsizeRaising` at `heapInsert`, `heapPop`, and `lenVal` | same workers | shared raising conversion with CPython's exact `OverflowError`; the sequence-subscript `PyExc_IndexError` variant is `pySsizeIndex`/`indexErrorSize`. |
| `Python/ceval.c:_PyEval_SliceIndex` (index protocol, then signed-size clipping) | `pySsizeClamping`, `asSliceIdx`, `normIndex` | shared | slice bounds clip to the pinned signed 64-bit range before ordinary sequence normalization. |
| `Objects/floatobject.c:PyFloat_AsDouble` and `Objects/longobject.c:PyLong_AsDouble` (left conversion, right conversion, then operation) | `floatNumber` / `Float64.fromInt`; integer true division uses `Float64.divideInt` directly | shared through `evalBinOp` | Mixed division and negative or mixed-float power preserve conversion order. Portable zero, infinity, and unit-base power cases are decided; NaN payload, complex, and platform-libm `pow` cases stay loud. |
| `Objects/abstract.c:PyObject_GetIter`, then `PyIter_Next` | `rangeVals`, `heapContains`, `execFor*`, and generator steppers | `iterValues`, `Kont` cursors, and `exec*` shells | **Closed for the admitted value/cursor domain:** `iterValues_rangeVals` proves the shared immediate range worker; `iteration_probe.py` covers range, tuple, and live list growth in both interpreters. Generator and dictionary mutation remain explicit stateful cursors, following their distinct CPython iterator objects. |
| `Objects/abstract.c:PyObject_Size` (sequence/mapping length) | `lenVal`, `lenValH`, `heapLen` | `lenM`, `liftRes` | shared; `len(range(...))` narrows the computed result through `pySsizeRaising`. |
| `Objects/abstract.c:PyObject_GetItem` / `PyObject_SetItem` | `indexValH`, `heapIndex`, `assignToH` | `indexM`, `assignM` | shared receiver-specific heap paths; list and dict errors retain their CPython classes/messages. |
| `Objects/object.c:PyObject_Str` / `PyObject_Repr`, and `Objects/listobject.c`/`dictobject.c` container renderers | `strOfVal`, `reprVal`, `printOne` | the same rendering workers through `applyBuiltin` and `emit` | **Closed for the admitted overlap:** `strOfValH_basic` proves heap-aware `str()` delegates the four immediate scalar cases to `strOfVal`; `render_probe.py` covers scalar `str`, tuple `repr`, and list `repr` in both interpreters. Sets, identity objects, unsupported Unicode rendering, and unbounded recursion remain loud. |
| `Include/internal/pycore_ceval.h:Py_EnterRecursiveCall` at each C frame (with matching leave) | `pythonRecursionFull` plus call, argument-binding, exception, comparison, builtin, generator, and class-construction checks | the same predicate through `callInM`, `withFrameRecursionUnit`, `withWorldRecursionUnit`, and `richCompareRecursionCheckH` | **Closed:** `python_frame_then_c_boundary` proves the Python-frame and nested C-call predicates differ at the pinned boundary; `recursive_entry_probe.py` covers int/str calls at shallow and boundary depths in both interpreters. The normalized `World.callDepth` and pinned limit 1000 cover admitted sites; direct rendering beyond `reprFuel` remains a declared refusal. |
| extractor `ACCELERATOR_ADMISSIONS` (native import, then guarded call domain) | structured admission metadata | extraction shared by both surfaces | `_bisect` is guarded after the measured `hi=-1` divergence; `_stat` and `_opcode` remain explicitly unadmitted where equivalence is not established. |

The census therefore records five protocol families with more than one Lean
worker (`RichCompareBool`, hash/equality key lookup, iteration, rendering, and
recursive entry). Those splits are now named rather than hidden behind the word
"shared". A future admission must either route all observers through one
worker or add a theorem and a domain row explaining why the split is exact.

The two interpreter control surfaces now have a first compositional adequacy
edge: `Monadic.twinAgrees_evalOpenList_constants` proves by induction on an
arbitrary-length expression list that the fuel-free monadic list walker and the
trunk's fuelled `evalExprs` agree for constant lists whenever the strict list
length fuel bound holds. This composes the literal bridge with left-to-right
list control without adding another per-operator refinement lemma.
`Monadic.twinAgrees_evalOpenList_of_each` factors that induction into a
reusable composition theorem: any pointwise expression bridge, quantified over
the continuation state and positive remaining fuel, lifts to the whole list.
`Monadic.twinAgrees_execOpenList_of_each` supplies the matching statement
sequencing theorem, preserving the updated state after `.next` and the early
`.brk`, `.cont`, `.ret`, exception, timeout, and refusal flows. Calls and
stateful script control remain the next adequacy boundary. At the call entry,
`Monadic.twinAgrees_callIn_missing_function` now closes the preflight branch:
for a positive fuel and an absent function table entry, both interpreters
return the same depth-normalized `NameError` without changing the world.
`Monadic.twinAgrees_callIn_unsupported_args` closes the next ordered preflight
branch when the function has unsupported parameter features and the generator
capture guard is clear; both surfaces return the same loud refusal before body
execution. `Monadic.twinAgrees_callIn_arity_error` now closes the arity branch
as well, including the depth-sensitive CPython diagnostic and retained world.
`Monadic.twinAgrees_callIn_static_locals` closes the following static-locals
refusal branch before body execution.
`Monadic.twinAgrees_callIn_zero_fuel` also pins the shared timeout boundary for
every call shape.
The substrate now exposes kernel-checked `Monadic.toRun_set` and
`Monadic.toRun_modify` equations beside `toRun_get`/`toRun_bind`, so positive
fuel calls and scripts share one state-wrapper boundary.
`Monadic.toRun_liftState` extends that boundary across the `StateT`-to-`ExceptT`
frame lift, preserving timeout, refusal, exception, and success projections.
`Monadic.toRun_bind_ok` factors the successful bind projection used by
`tryCatch` and call unwinding, so those proofs can stay at the `Run` boundary.
`Monadic.toRun_tryCatch_ok` specializes the same projection to a successful
protected action, preserving its returned state and value through the handler
layer.
`Monadic.twinAgrees_execOpenList_nil` and its world projection close the empty
statement-body base case consumed by ordinary call entry.
`Run.finishCallAt_ok` pins the successful trunk-side call-depth restoration
that the monadic `finishCallM` must match.
`Run.finishCallAt_exn` pins the corresponding raised-exception unwind, keeping
the world observable while restoring the requested depth.
`Monadic.finishCallM_pure_ok` composes the state-retaining try/catch and modify
projections for a pure successful body, restoring call depth on the monadic
surface as well.
`Monadic.finishCallM_empty_body_ok` composes the same restoration with the
actual empty `execOpenList` body and its `inWorld` projection.
`Monadic.finishCallM_pass_body_ok` extends this composition to the first
nonempty statement body, a one-statement `pass` sequence.
`Monadic.finishCallM_expr_constant_body_ok` covers the first effectful body:
an expression statement evaluating an integer constant before completion.
`Monadic.finishCallM_modify_ok` is the first state-mutating call theorem: an
arbitrary world mutation threads through restoration while preserving the
mutated heap/global/output/clock fields.
`Monadic.leaveCallM_modify_ok` covers the matching nested-call unwind: an
arbitrary mutation is followed by the active frame's depth decrement while
the mutated world remains observable.

## Operator dispatch

| Source arm | CPython entry and protocol order | Trunk | Runner | Domain / remaining gap |
|---|---|---|---|---|
| `+`, `-`, `*`, `/`, `//`, `%`, `**`, shifts, bitwise ops | `Objects/abstract.c:PyNumber_*` (numeric dispatch, then operand conversion); string `%` uses `PyUnicode_Format`; power uses `float_pow` for floating paths | `evalBinOp`; heap `evalBinOpH` for refs | `binOpM` / `evalOpen` | shared arithmetic workers; bare and measured-width string conversions are live, while precision, mapping keys, complex results, and platform `pow` remain loud. |
| unary `+`, `-`, `~`, `not` | `PyNumber_Positive`, `PyNumber_Negative`, `PyNumber_Invert`, or `PyObject_IsTrue` for `not` | `evalUnaryOp`, `evalUnaryOpH` | `unaryOpM` | `not` delegates to shared truthiness. |
| `==`, `!=`, `<`, `<=`, `>`, `>=` | `PyObject_RichCompare` (container implementations call `PyObject_RichCompareBool` for element equality) | `evalCompareOpH`, `ordFromLt` | `evalCompareChainM` → shared `evalCompareOpH` | value and heap workers are explicit; non-finite container comparisons refuse because immediate identity is not represented. |
| `is`, `is not` | `Py_Is`/pointer identity in the comparison opcode; no value comparison | identity arms of `evalCompareOpH` | identity arms of `evalCompareChainM` | refs, `None`, and singleton markers are exact; other immediate identity is loud. |
| `in`, `not in` | `PySequence_Contains` or mapping key lookup; each element probe uses `PyObject_RichCompareBool` | `valContains`, `heapContains` | shared through `evalCompareChainM` | strings, tuples/lists, and dict/set keys are admitted; generator membership remains stateful/loud. |

## Builtin arms

Both surfaces expose the following names. The runner dispatch is in
`Monadic.Eval.applyBuiltin`; the trunk dispatch is its `evalExpr` call arm.
The middle column records the CPython entry point and the protocol sequence
that the worker must preserve.

| Builtin arm | CPython entry and protocol order | Trunk / runner worker | Current boundary |
|---|---|---|---|
| `len` | `builtin_len` → `PyObject_Size` | `lenValH` / `heapLen`; `lenM` | signed-size narrowing is pinned; unsupported objects refuse. |
| `abs`, `int`, `float`, `bool`, `round` | `builtin_abs`, `PyNumber_Long`, `PyNumber_Float`, `PyObject_IsTrue`, `builtin_round` (conversion, then admitted numeric method frame) | scalar conversion, truthiness, and rounding workers | scalar domain is live; unsupported protocols and unmodeled frames refuse. |
| `divmod`, `pow` | `builtin_divmod` / `PyNumber_Divmod`; `builtin_pow` / `PyNumber_Power` (argument conversion before arithmetic) | `divmodVal`, `powModArgs`, `evalBinOp .pow` | integer modular slice and portable power cases are live; platform `pow` remains loud. |
| `range` | `range_constructor` (argument `__index__`, then size computation) | `rangeMake`, `rangeVals` | range bounds and result narrowing use the shared index workers. |
| `sorted` | `builtin_sorted` → `PySequence_List`/`PyList_Sort` → rich comparison | `sortedValH`, `sortByLt` | list materialization and stable `rvalLt` are live; non-finite comparison and unsupported key/cmp paths refuse. |
| `max`, `min` | `builtin_min_max` → `PyObject_RichCompareBool` for each candidate | `extremumValH`, `rvalLt` | argument order and comparison recursion are pinned; unsupported ordering refuses. |
| `sum` | `builtin_sum` → iterator protocol and numeric addition | `sumFold` and iterator dispatch | admitted scalar and iterator paths are live; unsupported additions refuse. |
| `tuple`, `list`, `set`, `dict` | constructors drain `PyObject_GetIter`; list/dict/set constructors allocate and may hash or compare keys | iterator workers plus allocation workers | modeled allocation budgets replace environment-dependent exhaustion; unsupported pair/key forms refuse. |
| `any`, `all` | `builtin_any`/`builtin_all` → `PyObject_IsTrue` for each iterator item | `anyAllScan` or stateful generator cursor | short circuit and generator state are explicit. |
| `next`, `iter`, `enumerate`, `count` | iterator constructor/`tp_iternext`, including `StopIteration` | generator/iterator step workers | admitted generators are stateful; unsupported delegation remains loud. |
| `ord`, `chr`, `ascii`, `hex`, `oct`, `bin`, `format`, `str`, `repr` | scalar conversion and `PyObject_Str`/`PyObject_Repr` | scalar and rendering workers | printable scalar/container inventory is shared; sets and identity objects refuse. |
| `print` | `builtin_print` → `PyObject_Str`/`PyFile_WriteObject` in argument order | stdout-aware trunk arm; `strOfArgs`/`emit` in runner | stdout is visible only through stateful/script surfaces; kwargs and unsupported rendering remain loud. |
| internal `<dictdel>`, `<attrdel>`, f-string and star markers | extractor marker arms, not Python-name lookup | explicit synthetic boundaries | source-level shadows cannot change these internal dispatches; native source-node semantics remain follow-up work. |

## Method arms

| Method arm | CPython entry and protocol order | Trunk / runner worker | Current boundary |
|---|---|---|---|
| dict `.get`, `.keys`, `.values`, `.items`, `.clear` | `dict_get`, `dict_keys`, `dict_values`, `dict_items`, `dict_clear`; key methods hash/probe before returning a view | heap dict/view workers and live view cursors | dict lookup, mutation, and live views are admitted; unsupported view operations refuse. |
| list `.append`, `.pop`, `.insert` | `list_append`, `list_pop`, `list_insert`; index arguments use `PyNumber_Index` then the raising or clamping size conversion | `heapAppend`, `heapPop`, `heapInsert` | raising/clamping workers are shared and endpoint-tested; allocation limits remain loud. |
| str `.swapcase`, `.isupper`, `.islower`, `.upper`, `.index`, `.join` | Unicode methods, with `.index` raising after a search and `.join` draining an iterable | string workers and iterator drain | admitted Unicode 3.9 table is live; unsupported Unicode/rendering forms refuse. |
| float `.is_integer` | `float_is_integer` on the binary64 value | `floatIsInteger` | binary64 word semantics are shared. |
| admitted instance methods and namedtuple methods | descriptor lookup, bound `self`, then `PyObject_Call` | `callIn` / class and tuple dispatch | qualified method entries and static namedtuple recognition remain architectural boundaries; runtime class/namedtuple values are the follow-up. |

## Work list produced by the census

The remaining protocol work is now explicit. Rich comparison has multiple
context workers and needs either one shared worker or a refinement/domain
theorem before widening identity-sensitive values. Hash/key probes and
rendering have the same obligation. The index workers already separate raising
and clamping conversions; the float conversion worker is shared, but platform
`pow` remains refused. Recursive entry is shared as a predicate, with direct
rendering beyond `reprFuel` still outside the decided domain. The runner and
trunk control/transport wrappers remain separate and do not yet have a full
recursive expression, statement, or script adequacy theorem.

The nonempty control-flow bridge `Monadic.finishCallM_ret_constant_body_ok`
also covers a one-statement `return 1` body, preserving `RFlow.ret` through
the same world and depth restoration boundary.

Its bare-return counterpart, `Monadic.finishCallM_ret_none_body_ok`, preserves
the `RFlow.ret .none` channel through the same boundary.

The loop-control bridge `Monadic.finishCallM_break_body_ok` preserves
`RFlow.brk` through the boundary as well; enclosing-loop handling remains in
the continuation layer.

The corresponding `Monadic.finishCallM_continue_body_ok` bridge preserves
`RFlow.cont`; loop re-testing remains owned by the continuation layer.

The two-statement sequencing bridge `Monadic.finishCallM_pass_expr_body_ok`
composes `pass` followed by an integer expression statement through the same
left-to-right body walker and restoration boundary.

`Monadic.finishCallM_pass_ret_body_ok` covers the corresponding early-return
sequence, proving that the second statement's `RFlow.ret` stops the body walk.

`Monadic.finishCallM_pass_break_body_ok` covers normal sequencing into a
`break`, preserving `RFlow.brk` for the enclosing loop shell.

`Monadic.finishCallM_pass_continue_body_ok` covers the matching normal-to-
`continue` sequence and preserves `RFlow.cont`.

`Monadic.finishCallM_three_pass_body_ok` checks a three-statement normal body,
showing that the sequence walker composes beyond the two-statement cases.

`Monadic.finishCallM_four_pass_body_ok` extends the same kernel-checked
normal sequencing to four statements.

`Monadic.finishCallM_five_pass_body_ok` extends normal sequencing to five
statements.

`Monadic.finishCallM_four_pass_ret_body_ok` extends early-return sequencing
to four normal statements followed by a return.

`Monadic.finishCallM_pass_assign_empty_locals_body_ok` is the first assignment
sequencing bridge with an explicit empty frame-local environment; the body
updates its local binding and still returns normal after projection to `World`.

`Monadic.finishCallM_assign_existing_local_body_ok` covers assignment to an
already-bound local, preserving the same normal-flow and depth result.

`Monadic.finishCallM_assign_existing_local_ret_body_ok` composes that local
update with a following constant return, checking assignment state threading
into early flow.

`Monadic.finishCallM_assign_existing_local_pass_body_ok` checks the symmetric
normal continuation after the local assignment.

`Monadic.finishCallM_assign_existing_local_break_body_ok` composes the local
assignment into `RFlow.brk` for the enclosing loop shell.

`Monadic.finishCallM_assign_existing_local_continue_body_ok` composes the
same local assignment into `RFlow.cont`.

`Monadic.finishCallM_assign_existing_local_ret_none_body_ok` composes the
assignment into bare-return flow, preserving `RFlow.ret .none`.

`Monadic.finishCallM_assign_existing_local_expr_body_ok` composes the local
assignment into a following normal expression statement.

`Monadic.finishCallM_assign_two_existing_locals_body_ok` checks two successive
existing-local assignments, threading both updates through normal completion.

`Monadic.finishCallM_assign_three_existing_locals_body_ok` extends the same
state threading to three successive assignments.

`Monadic.finishCallM_assign_existing_local_ret_pass_body_ok` checks that a
return after assignment short-circuits a trailing statement.

`Monadic.finishCallM_three_pass_ret_body_ok` extends early-return sequencing
to three normal statements followed by a return.

`Monadic.finishCallM_three_pass_break_body_ok` extends break-flow sequencing
to three normal statements followed by `break`.

`Monadic.finishCallM_three_pass_continue_body_ok` extends continue-flow
sequencing to three normal statements followed by `continue`.

`Monadic.finishCallM_three_pass_ret_none_body_ok` extends bare-return
sequencing to three normal statements followed by `return`.

`Monadic.finishCallM_assign_two_existing_locals_ret_body_ok` extends
assignment return short-circuiting to two successive local updates.

`Monadic.finishCallM_assign_three_existing_locals_ret_body_ok` extends it to
three successive local updates followed by a return.

`Monadic.finishCallM_assign_three_existing_locals_pass_body_ok` checks the
normal continuation after those three updates.

`Monadic.finishCallM_assign_three_existing_locals_expr_body_ok` checks the
normal expression continuation after the three updates.

`Monadic.finishCallM_assign_four_existing_locals_body_ok` extends normal
assignment state threading to four successive local updates.

`Monadic.finishCallM_assign_four_existing_locals_ret_body_ok` extends the same
four-update bridge through an early value return.

`Monadic.finishCallM_assign_four_existing_locals_pass_body_ok` extends the
four-update bridge through a normal `pass` continuation.

`Monadic.finishCallM_assign_four_existing_locals_expr_body_ok` extends the
four-update bridge through a normal integer expression statement.

`Monadic.finishCallM_assign_four_existing_locals_ret_none_body_ok` extends the
four-update bridge through a bare return.

`Monadic.finishCallM_assign_four_existing_locals_break_body_ok` extends the
four-update bridge through an abrupt `break` flow.

`Monadic.finishCallM_assign_four_existing_locals_continue_body_ok` extends the
four-update bridge through an abrupt `continue` flow.

`Monadic.finishCallM_assign_five_existing_locals_body_ok` extends normal
assignment state threading to five successive local updates.

`Monadic.finishCallM_assign_five_existing_locals_ret_body_ok` extends the
five-update bridge through an early value return.

`Monadic.finishCallM_assign_five_existing_locals_pass_body_ok` extends the
five-update bridge through a normal `pass` continuation.

`Monadic.finishCallM_assign_five_existing_locals_expr_body_ok` extends the
five-update bridge through a normal integer expression statement.

`Monadic.finishCallM_assign_five_existing_locals_ret_none_body_ok` extends the
five-update bridge through a bare return.

`Monadic.finishCallM_assign_five_existing_locals_break_body_ok` extends the
five-update bridge through an abrupt `break` flow.

`Monadic.finishCallM_assign_five_existing_locals_continue_body_ok` extends the
five-update bridge through an abrupt `continue` flow.

`Monadic.finishCallM_assign_six_existing_locals_body_ok` extends normal
assignment state threading to six successive local updates.

`Monadic.finishCallM_assign_six_existing_locals_ret_body_ok` extends the
six-update bridge through an early value return.

`Monadic.finishCallM_assign_six_existing_locals_pass_body_ok` extends the
six-update bridge through a normal `pass` continuation.

`Monadic.finishCallM_assign_six_existing_locals_expr_body_ok` extends the
six-update bridge through a normal integer expression statement.

`Monadic.finishCallM_assign_six_existing_locals_ret_none_body_ok` extends the
six-update bridge through a bare return.

`Monadic.finishCallM_assign_six_existing_locals_break_body_ok` extends the
six-update bridge through an abrupt `break` flow.

`Monadic.finishCallM_assign_six_existing_locals_continue_body_ok` extends the
six-update bridge through an abrupt `continue` flow.

`Monadic.finishCallM_assign_seven_existing_locals_body_ok` extends normal
assignment state threading to seven successive local updates.

`Monadic.finishCallM_assign_seven_existing_locals_ret_body_ok` extends the
seven-update bridge through an early value return.

`Monadic.finishCallM_assign_seven_existing_locals_pass_body_ok` extends the
seven-update bridge through a normal `pass` continuation.

`Monadic.finishCallM_assign_seven_existing_locals_expr_body_ok` extends the
seven-update bridge through a normal integer expression statement.

`Monadic.finishCallM_assign_seven_existing_locals_ret_none_body_ok` extends the
seven-update bridge through a bare return.

`Monadic.finishCallM_assign_seven_existing_locals_break_body_ok` extends the
seven-update bridge through an abrupt `break` flow.

`Monadic.finishCallM_assign_seven_existing_locals_continue_body_ok` extends the
seven-update bridge through an abrupt `continue` flow.

`Monadic.finishCallM_assign_eight_existing_locals_body_ok` extends normal
assignment state threading to eight successive local updates.

`Monadic.finishCallM_assign_eight_existing_locals_ret_body_ok` extends the
eight-update bridge through an early value return.

`Monadic.finishCallM_assign_eight_existing_locals_pass_body_ok` extends the
eight-update bridge through a normal `pass` continuation.

`Monadic.finishCallM_assign_eight_existing_locals_expr_body_ok` extends the
eight-update bridge through a normal integer expression statement.

`Monadic.finishCallM_assign_eight_existing_locals_ret_none_body_ok` extends the
eight-update bridge through a bare return.

`Monadic.finishCallM_assign_eight_existing_locals_break_body_ok` extends the
eight-update bridge through an abrupt `break` flow.

`Monadic.finishCallM_assign_eight_existing_locals_continue_body_ok` extends the
eight-update bridge through an abrupt `continue` flow.

`Monadic.finishCallM_assign_nine_existing_locals_body_ok` extends normal
assignment state threading to nine successive local updates.

`Monadic.finishCallM_assign_nine_existing_locals_ret_body_ok` extends the
nine-update bridge through an early value return.

`Monadic.finishCallM_assign_nine_existing_locals_pass_body_ok` extends the
nine-update bridge through a normal `pass` continuation.

`Monadic.finishCallM_assign_nine_existing_locals_expr_body_ok` extends the
nine-update bridge through a normal integer expression statement.

`Monadic.finishCallM_assign_nine_existing_locals_ret_none_body_ok` extends the
nine-update bridge through a bare return.

`Monadic.finishCallM_assign_nine_existing_locals_break_body_ok` extends the
nine-update bridge through an abrupt `break` flow.

`Monadic.finishCallM_assign_nine_existing_locals_continue_body_ok` extends the
nine-update bridge through an abrupt `continue` flow.

`Monadic.finishCallM_assign_ten_existing_locals_body_ok` extends normal
assignment state threading to ten successive local updates.

`Monadic.finishCallM_assign_ten_existing_locals_ret_body_ok` extends the
ten-update bridge through an early value return.

`Monadic.finishCallM_assign_ten_existing_locals_pass_body_ok` extends the
ten-update bridge through a normal `pass` continuation.

`Monadic.finishCallM_assign_ten_existing_locals_expr_body_ok` extends the
ten-update bridge through a normal integer expression statement.

`Monadic.finishCallM_assign_ten_existing_locals_ret_none_body_ok` extends the
ten-update bridge through a bare return.

`Monadic.finishCallM_assign_ten_existing_locals_break_body_ok` extends the
ten-update bridge through an abrupt `break` flow.

`Monadic.finishCallM_assign_ten_existing_locals_continue_body_ok` extends the
ten-update bridge through an abrupt `continue` flow.

`Monadic.finishCallM_assign_eleven_existing_locals_body_ok` extends normal
assignment state threading to eleven successive local updates.

`Monadic.finishCallM_assign_eleven_existing_locals_ret_body_ok` extends the
eleven-update bridge through an early value return.

`Monadic.finishCallM_assign_eleven_existing_locals_pass_body_ok` extends the
eleven-update bridge through a normal `pass` continuation.

`Monadic.finishCallM_assign_eleven_existing_locals_expr_body_ok` extends the
eleven-update bridge through a normal integer expression statement.

`Monadic.finishCallM_assign_eleven_existing_locals_ret_none_body_ok` extends
the eleven-update bridge through a bare return.

`Monadic.finishCallM_assign_eleven_existing_locals_break_body_ok` extends the
eleven-update bridge through an abrupt `break` flow.

`Monadic.finishCallM_assign_eleven_existing_locals_continue_body_ok` extends
the eleven-update bridge through an abrupt `continue` flow.

`Monadic.finishCallM_assign_twelve_existing_locals_body_ok` extends normal
assignment state threading to twelve successive local updates.

`Monadic.finishCallM_assign_twelve_existing_locals_ret_body_ok` extends the
twelve-update bridge through an early value return.

`Monadic.finishCallM_assign_twelve_existing_locals_pass_body_ok` extends the
twelve-update bridge through a normal `pass` continuation.

`Monadic.finishCallM_assign_twelve_existing_locals_expr_body_ok` extends the
twelve-update bridge through a normal integer expression statement.

`Monadic.finishCallM_assign_twelve_existing_locals_ret_none_body_ok` extends
the twelve-update bridge through a bare return.

`Monadic.finishCallM_assign_twelve_existing_locals_break_body_ok` extends the
twelve-update bridge through an abrupt `break` flow.

`Monadic.finishCallM_assign_twelve_existing_locals_continue_body_ok` extends
the twelve-update bridge through an abrupt `continue` flow.

`Monadic.finishCallM_assign_thirteen_existing_locals_body_ok` extends normal
assignment state threading to thirteen successive local updates.

`Monadic.finishCallM_assign_thirteen_existing_locals_ret_body_ok` extends the
thirteen-update bridge through an early value return.

`Monadic.finishCallM_assign_thirteen_existing_locals_pass_body_ok` extends the
thirteen-update bridge through a normal `pass` continuation.

`Monadic.finishCallM_assign_thirteen_existing_locals_expr_body_ok` extends the
thirteen-update bridge through a normal integer expression statement.

`Monadic.finishCallM_assign_thirteen_existing_locals_ret_none_body_ok` extends
the thirteen-update bridge through a bare return.

`Monadic.finishCallM_assign_thirteen_existing_locals_break_body_ok` extends the
thirteen-update bridge through an abrupt `break` flow.

`Monadic.finishCallM_assign_thirteen_existing_locals_continue_body_ok` extends
the thirteen-update bridge through an abrupt `continue` flow.

`Monadic.finishCallM_assign_fourteen_existing_locals_body_ok` extends normal
assignment state threading to fourteen successive local updates.

`Monadic.finishCallM_assign_fourteen_existing_locals_ret_body_ok` extends the
fourteen-update bridge through an early value return.

`Monadic.finishCallM_assign_fourteen_existing_locals_pass_body_ok` extends the
fourteen-update bridge through a normal `pass` continuation.

`Monadic.finishCallM_assign_fourteen_existing_locals_expr_body_ok` extends the
fourteen-update bridge through a normal integer expression statement.

`Monadic.finishCallM_assign_fourteen_existing_locals_ret_none_body_ok` extends
the fourteen-update bridge through a bare return.

`Monadic.finishCallM_assign_fourteen_existing_locals_break_body_ok` extends the
fourteen-update bridge through an abrupt `break` flow.

`Monadic.finishCallM_assign_fourteen_existing_locals_continue_body_ok` extends
the fourteen-update bridge through an abrupt `continue` flow.

`Monadic.finishCallM_assign_fifteen_existing_locals_body_ok` extends normal
assignment state threading to fifteen successive local updates.

`Monadic.finishCallM_assign_fifteen_existing_locals_ret_body_ok` extends the
fifteen-update bridge through an early value return.

`Monadic.finishCallM_assign_fifteen_existing_locals_pass_body_ok` extends the
fifteen-update bridge through a normal `pass` continuation.

`Monadic.finishCallM_assign_fifteen_existing_locals_expr_body_ok` extends the
fifteen-update bridge through a normal integer expression statement.

`Monadic.finishCallM_assign_fifteen_existing_locals_ret_none_body_ok` extends
the fifteen-update bridge through a bare return.

`Monadic.finishCallM_assign_fifteen_existing_locals_break_body_ok` extends the
fifteen-update bridge through an abrupt `break` flow.

`Monadic.finishCallM_assign_fifteen_existing_locals_continue_body_ok` extends
the fifteen-update bridge through an abrupt `continue` flow.

`Monadic.finishCallM_assign_sixteen_existing_locals_body_ok` extends normal
assignment state threading to sixteen successive local updates.

`Monadic.finishCallM_assign_sixteen_existing_locals_ret_body_ok` extends the
sixteen-update bridge through an early value return.

`Monadic.finishCallM_assign_sixteen_existing_locals_pass_body_ok` extends the
sixteen-update bridge through a normal `pass` continuation.

`Monadic.finishCallM_assign_sixteen_existing_locals_expr_body_ok` extends the
sixteen-update bridge through a normal integer expression statement.

`Monadic.finishCallM_assign_sixteen_existing_locals_ret_none_body_ok` extends
the sixteen-update bridge through a bare return.

`Monadic.finishCallM_assign_sixteen_existing_locals_break_body_ok` extends the
sixteen-update bridge through an abrupt `break` flow.

`Monadic.finishCallM_assign_sixteen_existing_locals_continue_body_ok` extends
the sixteen-update bridge through an abrupt `continue` flow.

`Monadic.finishCallM_assign_seventeen_existing_locals_body_ok` extends normal
assignment state threading to seventeen successive local updates.

`Monadic.finishCallM_assign_seventeen_existing_locals_ret_body_ok` extends the
seventeen-update bridge through an early value return.

`Monadic.finishCallM_assign_seventeen_existing_locals_pass_body_ok` extends the
seventeen-update bridge through a normal `pass` continuation.

`Monadic.finishCallM_assign_seventeen_existing_locals_expr_body_ok` extends the
seventeen-update bridge through a normal integer expression statement.

`Monadic.finishCallM_assign_seventeen_existing_locals_ret_none_body_ok` extends
the seventeen-update bridge through a bare return.

`Monadic.finishCallM_assign_seventeen_existing_locals_break_body_ok` extends the
seventeen-update bridge through an abrupt `break` flow.

`Monadic.finishCallM_assign_seventeen_existing_locals_continue_body_ok` extends
the seventeen-update bridge through an abrupt `continue` flow.

`Monadic.finishCallM_assign_eighteen_existing_locals_body_ok` extends normal
assignment state threading to eighteen successive local updates.

`Monadic.finishCallM_assign_eighteen_existing_locals_ret_body_ok` extends the
eighteen-update bridge through an early value return.

`Monadic.finishCallM_assign_eighteen_existing_locals_pass_body_ok` extends the
eighteen-update bridge through a normal `pass` flow.

`Monadic.finishCallM_assign_eighteen_existing_locals_expr_body_ok` extends the
eighteen-update bridge through a normal expression statement.

`Monadic.finishCallM_assign_eighteen_existing_locals_ret_none_body_ok` extends the
eighteen-update bridge through an early bare return.

`Monadic.finishCallM_assign_eighteen_existing_locals_break_body_ok` extends the
eighteen-update bridge through abrupt `break` flow.

`Monadic.finishCallM_assign_eighteen_existing_locals_continue_body_ok` extends the eighteen-update bridge through abrupt `continue` flow.

`Monadic.finishCallM_assign_nineteen_existing_locals_body_ok` extends normal assignment state threading to nineteen successive local updates.

`Monadic.finishCallM_assign_nineteen_existing_locals_ret_body_ok` extends the nineteen-update bridge through an early value return.

`Monadic.execOpenList_assignments_next` and
`Monadic.execOpenList_assignments_threaded`, with the
`finishCallM_assignments_body_ok` wrapper, provide induction theorems for
arbitrary finite assignment lists and explicit frame-state threading;
fixed-count assignment bridges are no longer the work item.

The generic value-return wrapper is parked pending a raw `execOpenList` append/
return composition lemma; the fixed-count matrix remains closed.

`Monadic.execOpenList_assignments_ret_run` supplies the arbitrary-list append/
return composition at the established `toRun` boundary.

`Monadic.finishCallM_assignments_ret_run` lifts arbitrary-list value-return composition through `inWorld` and call-depth restoration.

`Monadic.execOpenList_assignments_pass_run` extends arbitrary assignment-list composition through a final normal pass flow.

`Monadic.finishCallM_assignments_pass_run` lifts arbitrary-list pass composition through `inWorld` and call-depth restoration.

`Monadic.execOpenList_assignments_expr_run` and `Monadic.finishCallM_assignments_expr_run` cover arbitrary assignment-list expression flow at both interpreter boundaries.

`Monadic.execOpenList_assignments_bare_ret_run` and `Monadic.finishCallM_assignments_bare_ret_run` cover arbitrary assignment-list bare-return flow at both interpreter boundaries.

`Monadic.execOpenList_assignments_break_run` and `Monadic.finishCallM_assignments_break_run` cover arbitrary assignment-list break flow at both interpreter boundaries.

`Monadic.execOpenList_assignments_continue_run` and `Monadic.finishCallM_assignments_continue_run` cover arbitrary assignment-list continue flow at both interpreter boundaries.


The generic `finishCallM` transport, the four-result normalization attempt, and the combined handler transport remain parked at the substrate: unfolding `ExceptT.tryCatch` leaves a `StateT.bind` continuation match that does not reduce under arbitrary handler results. Assignment-list flow coverage remains complete.

`Monadic.toRun_tryCatch_timeout` and `Monadic.toRun_tryCatch_unsupported` close the timeout/refusal projections of the shared `tryCatch` substrate.

The remaining recursive call/body adequacy debt is the `callInM` body branch's
`finishCallM`/`leaveCallM` transport and four-flow mapping; assignment-list
composition is complete, while generic `StateT.bind` handler normalization is
still open.

`toRun_tryCatch_handler_ok`, `toRun_tryCatch_handler_timeout`, and `toRun_tryCatch_handler_unsupported` close the explicit handler-result projections for protected Python exceptions.

`Monadic.finishCallM_of_ok` and `Monadic.finishCallM_of_exn` provide explicit-result call-boundary transport for successful and exceptional protected actions.

`Monadic.finishCallM_of_timeout` and `Monadic.finishCallM_of_unsupported` complete explicit-result call transport for timeout and refusal outcomes.

`Monadic.finishCallM_inWorld_of_ok` applies explicit success restoration to a known frame action result, covering the ordinary `callInM` body boundary.

`Monadic.finishCallM_inWorld_of_exn` applies explicit exception restoration to a known frame action result at the `callInM` body boundary.

`Monadic.finishCallM_inWorld_of_timeout` and `Monadic.finishCallM_inWorld_of_unsupported` complete explicit timeout/refusal transport at the `callInM` frame/world boundary.

`Monadic.toRun_get_bind` and `Monadic.toRun_set_bind` normalize state getter/setter binds for direct call-plan adequacy proofs.

`Monadic.twinAgrees_callInM_top_assignments` composes the arbitrary assignment-list
normal-flow induction with the top-depth call boundary. The corresponding
`_ret`, `_pass`, `_break`, and `_continue` theorems cover every ordinary flow
for an assignment prefix, preserving the post-body world or the faithful
outside-loop refusal. `Monadic.execOpenList_assignments_exn_run` and
`Monadic.finishCallM_assignments_exn_run` add the matching arbitrary-list
exception induction, and `twinAgrees_callInM_top_assignments_exn` composes it
through the call boundary. The remaining recursive call/body debt is the
generic non-assignment-shaped body transport and handler congruence.

`Monadic.twinAgrees_callInM_top_body_next` closes the top-depth normal-flow
call branch for an arbitrary raw frame result, without restricting the body to
the assignment fragment. Its hypothesis names the exact frame state and
preserves the resulting world through `finishCallM`; the remaining generic
work is the other body flow classes and the recursive call continuation.

`Monadic.twinAgrees_callInM_top_body_ret` composes the same arbitrary raw body
result transport for a returned value, preserving the resulting world and
restoring the top call depth before exposing the value to the caller.

`Monadic.twinAgrees_callInM_top_body_break` composes the arbitrary raw body
transport for `RFlow.brk`; after restoring the top call depth, the top-level
call boundary produces the faithful `"'break' outside loop"` refusal.

`Monadic.twinAgrees_callInM_top_body_continue` provides the corresponding
arbitrary raw body transport for `RFlow.cont`, yielding the faithful
`"'continue' outside loop"` refusal at top-level call entry.

`Monadic.twinAgrees_callInM_top_body_exn` composes an arbitrary raw body
exception through the top-depth call boundary. The post-body world is retained,
the call depth is restored, and the original `PyErr` is propagated unchanged.

`Monadic.twinAgrees_callInM_top_body_timeout` and
`Monadic.twinAgrees_callInM_top_body_unsupported` complete the corresponding
timeout and classified-refusal body outcomes, preserving the exact refusal
message while keeping the top-depth boundary explicit.

`Monadic.leaveCallM_inWorld_of_ok` starts the recursive-call boundary
transport: an arbitrary successful frame action is projected through
`inWorld`, then `leaveCallM` decrements the resulting frame depth while
preserving the returned value.

`Monadic.leaveCallM_inWorld_of_exn` supplies the matching recursive exception
transport, retaining the post-body world, decrementing its active call depth,
and propagating the original Python error.

`Monadic.leaveCallM_inWorld_of_timeout` and
`Monadic.leaveCallM_inWorld_of_unsupported` complete the recursive
timeout/refusal projections; those outcomes carry no world and therefore need
no depth restoration.

`Monadic.twinAgrees_callInM_recursive_body_next` composes the generic
successful `leaveCallM` result with the non-top-depth `callInM` branch. Under
explicit depth and recursion-capacity guards, it restores the caller's frame
depth and maps `RFlow.next` to the returned `none` value.

`Monadic.twinAgrees_callInM_recursive_body_ret` composes the same guarded
recursive branch for `RFlow.ret v`, preserving the decremented post-body world
and returning `v` directly.

`Monadic.twinAgrees_callInM_recursive_body_break` composes the guarded
recursive branch for `RFlow.brk`; after `leaveCallM` restores the caller depth,
the call boundary yields the faithful `"'break' outside loop"` refusal.

`Monadic.twinAgrees_callInM_recursive_body_continue` supplies the corresponding
guarded recursive transport for `RFlow.cont`, yielding the faithful
`"'continue' outside loop"` refusal.

`Monadic.twinAgrees_callInM_recursive_body_exn` composes the guarded recursive
branch for a Python exception, retaining the post-body world, decrementing its
active depth, and propagating the original error.

`Monadic.twinAgrees_callInM_recursive_body_timeout` and
`Monadic.twinAgrees_callInM_recursive_body_unsupported` complete recursive
timeout/refusal mapping; these outcomes carry no world and therefore bypass
depth restoration while preserving timeout and refusal-message observations.

The branch transport matrix is now complete. The remaining recursive adequacy
debt is fuel-indexed: `kont` supplies the recursive continuation used by
`callInM`, while the branch theorems assume a raw `execOpenList` result at an
arbitrary `K`. `callInMono_eq_ofHalt` projects a completed run but does not yet
relate the fuel-indexed continuation to those body premises. The next theorem
must state that mutual refinement or explicitly record the raw-run bridge.

`Monadic.kont_call_succ` records the first fuel-indexed seam: the successor
`Kont.call` field delegates definitionally to `callInM (kont m fuel)`. The
remaining obligation is therefore the body-result relation at that continuation,
not call dispatch.

`Monadic.callInMono_succ` exposes the same seam at the public runner boundary:
successor-fuel `callInMono` is definitionally the `toRun` projection of that
`callInM` continuation at the normalized top depth.

`Monadic.callInMono_succ_body_next` composes that public seam with the generic
top-depth `.next` branch. Given the explicit raw `execOpenList` body result, it
now yields a direct `callInMono` result at successor fuel; the recursive body
relation itself remains a separate premise.

`Monadic.callInMono_succ_body_ret` provides the corresponding public
successor-fuel composition for an explicit `RFlow.ret v` body result and
returns `v` after restoring the normalized top depth.

`Monadic.callInMono_succ_body_break` composes the public successor-fuel seam
with the explicit `RFlow.brk` body result and produces the faithful
`"'break' outside loop"` refusal.

`Monadic.callInMono_succ_body_continue` completes the public successor-fuel
flow mappings for explicit body results by producing the faithful
`"'continue' outside loop"` refusal from `RFlow.cont`.

`Monadic.callInMono_succ_body_exn` adds the corresponding public successor-fuel
composition for a Python exception, preserving the post-body world and the
original error at normalized top depth.

`Monadic.callInMono_succ_body_timeout` and
`Monadic.callInMono_succ_body_unsupported` complete the public successor-fuel
body-result matrix for timeout and classified refusal, preserving timeout and
refusal-message observations.

`Monadic.callInMono_succ_empty_body` discharges the raw body premise for the
structural empty-body case. It is the first recursive refinement base case:
the successor-fuel public call returns `none` after the top-depth restoration,
with no per-count assignment bridge involved.

`Monadic.execOpenList_next_threaded` is the general nonempty-list induction
step: arbitrary statements with pointwise `.next` frame results compose while
threading the resulting `FrameState`. `Monadic.callInMono_succ_body_next_of_each`
then lifts that list induction through the public successor call, leaving only
the pointwise statement theorem as its premise.

`Monadic.execOpen_raw_of_toRun_next` and
`Monadic.execOpenList_next_threaded_of_toRun` invert successful `Run` projections
back to raw monadic results, so existing `toRun`-level statement bridges can
feed the state-threaded induction. `Monadic.callInMono_succ_body_next_of_toRun_each`
is the public successor composition using that inversion path.

`Monadic.execOpenList_raw_of_toRun_next` extends the inversion to an entire
statement list.  This keeps the successful `.next` body result available to
the raw `callInM` transport after a thresholded legacy-list comparison.

`Monadic.callInMono_succ_body_next_of_threshold` composes that threshold and
inversion with the public successor call.  It accepts an explicit legacy
`execStmts` `.next` result and produces the corresponding `callInMono` result,
leaving only the pointwise threshold premises to the caller.

`Monadic.callInMono_succ_body_pass_or_constants` discharges those premises for
an arbitrary body list whose nodes are passes or constant expression
statements.  Its list proof is length-parametric and uses the exact two-step
constant threshold; it does not enumerate body sizes.

`Monadic.twinAgrees_callIn_pass_body` is the first direct call-boundary
comparison.  For a normalized top-depth call whose body is one `pass`, it
relates the monadic successor runner to the legacy `callIn` result once the
legacy body has enough fuel for its statement step.

`Monadic.twinAgrees_callIn_pass_or_constants_body` lifts that comparison to an
arbitrary pass/constant body list.  The legacy frame uses `mkCallEnv` and
`markUnboundLocals`, while the monadic theorem uses `globalCallEnv`; the body
state-preservation induction reduces both to the same normalized caller world.

`Monadic.globalCallEnv_eq_legacy_of_noGlobal` gives the exact embedding needed
on the ordinary no-global fragment: when `hasGlobal` is false, the monadic
frame environment is definitionally the legacy `mkCallEnv` followed by
`markUnboundLocals`, with no extra global bindings.

`Monadic.globalCallEnv_eq_legacy_of_empty_globalNames` records the strongest
available extension for a `hasGlobal` frame without global names: if the
structured declaration census is empty, the global frame still reduces to the
same legacy environment.  Nonempty global bindings require a world-aware
legacy correspondence and are intentionally left explicit.

`Monadic.globalCallEnv_eq_worldFrame` makes that world-aware shape explicit:
the frame is `globalMarkedEnv` followed by the current world's values for each
declared name, then the parameter/default environment.  This is the exact
nonempty-global correspondence available to future body theorems; it does not
claim equality with a legacy frame that lacks those bindings.

`Monadic.globalAssignM_global_update` is the first global-operation bridge:
under the declaration marker, a scalar assignment updates both the module
global and the frame's marker-visible local binding.  Compound targets and
the legacy evaluator's corresponding global-write operation remain the next
world-state obligation.

`Monadic.frameGlobals_lookup_world` is the matching scalar-read equation: a
lookup through the frame's global view returns exactly the current
`World.globals` binding while leaving the frame state unchanged.

The attempted scalar-name expression bridge is deliberately not stated as an
`envGet` theorem: `envGet` is the local/cell lookup primitive and returns
`none` for a global-only name.  The global fallback is inline in `evalOpen` and
also depends on the module-global census, builtins, function tables, and the
name-error recursion check.  A sound expression adequacy theorem therefore
needs that combined resolver extracted or related to the legacy evaluator; a
local-only lemma would claim the wrong result for a declared global.

The static part itself is shared: both paths call the same `lookupG` over
`moduleGlobals m`.  The missing adequacy operation is the surrounding branch
that combines this result with the live frame-global view and the static
function/builtin/name-error cases.  Until that combined resolver relation is
stated, a standalone `lookupG` equality would be true but insufficient to
prove expression-level correspondence.

The legacy `evalExpr` and monadic `evalOpen` cases confirm the same ordering
for this fallback (static table, live globals, callable tables, builtins, then
the recursion-checked name error).  Their remaining mismatch is structural:
the legacy branch consumes explicit fuel and returns `Run`, while the monadic
branch runs in `SemF` and may carry a heap/world update.  No reusable theorem
currently packages that whole branch, so this item stops at the shared
operation boundary rather than introducing a parallel resolver.

`Monadic.nameErrorRecursionCheck_run` closes the reusable leaf at the end of
that branch: the monadic lift of the pinned recursion check is exactly the
legacy `Run.liftRes` worker.  The surrounding name-error branch still needs
the combined resolver relation described above.

`Monadic.nameError_after_recursion_check` composes that leaf with the final
exception arm: a full Python frame raises `RecursionError`, while a non-full
frame raises the requested `NameError`, with the frame state retained.  It is
independent of module lookup and is therefore reusable once the resolver
branch supplies its missing-value case.

The statically absent-name guard is already a direct shared predicate: both
interpreters test `lookupG (moduleGlobals m).1 id` for `none` before entering
the live-global and builtin branches.  Wrapping that test in a new definition
would add no correspondence information, so this item records no code change;
the remaining proof obligation is the surrounding branch composition.

The live-global leaf is likewise already closed by
`Monadic.frameGlobals_lookup_world`: it reads `World.globals` through the
frame without changing state.  There is no additional worker to prove here;
the unresolved theorem is only the conditional composition that chooses this
leaf after the static table misses.

The callable fallback is also structurally shared: after the static and live
global misses, both evaluators test `findFunction`, `findClass`,
`findNamedTuple`, and the builtin predicate in that order, returning the same
`.callable id` marker.  These are pure table predicates rather than a separate
worker; the remaining adequacy debt is still the enclosing branch relation.

The builtin-name leaf is shared through the authoritative `Ast.lean`
predicates: `isBuiltinName` yields the callable marker, while
`isPyBuiltinName` handles the later Python-builtin fallback.  Module-dunder
names are checked before that later fallback in both paths.  These predicates
are pure and already identical; only their placement inside the full resolver
awaits a cross-interpreter theorem.

The module-dunder refusal leaf uses the same message text in both interpreters:
`module attribute '<id>' is bound by the import machinery, not by a statement
— outside the G1 tier`.  Its only remaining mismatch is the standard refusal
projection (`SemF` retains an internal cause and snapshot while `Run` exposes
the message), so no message-only theorem is claimed without a raw refusal
premise.

The late Python-builtin fallback is shared through `isPyBuiltinName`; both
paths return `.callable id` for that predicate.  The adjacent lowered-builtin
refusal uses the common `unmodelledBuiltinMsg`, so its text is shared as well;
as with other refusals, only the internal-cause projection remains outside a
message-only theorem.

The smallest continuation relation needed for the remaining resolver proof is
an expression-level relation of the form
`toRun (evalOpen (kont m fuel) m e) st = evalExpr m fuel st e`, with the
`Kont`'s fuel field and every world/heap update threaded through the result.
The existing leaf bridges establish this for selected constants and operators,
but no generic expression induction currently packages the relation.  This is
the precise fuel/state mismatch preventing the resolver branch from advancing
the mutual theorem; adding a weaker value-only relation would lose state
correlations.

The first generalizable induction case is already present:
`Monadic.twinAgrees_evalOpen_constant` supplies the literal leaf, and
`Monadic.twinAgrees_evalOpenList_of_each` composes any pointwise expression
bridge over an arbitrary-length left-to-right list while threading each
resulting frame state.  This is the reusable control skeleton; the missing
work is supplying the generic expression-node bridge, not another fixed-size
literal matrix.

The first nonliteral case remains a genuine gap.  `Monadic.twinAgrees_evalOpen_unaryInt`
handles a unary operator only when its child is an integer literal; it cannot
feed the list-composition theorem for an arbitrary operand because the
`evalUnaryOpH` result must be related after the child has threaded an arbitrary
frame state.  Generalizing it requires a child bridge at `fuel - 1` plus the
heap-aware unary worker relation; extending the literal theorem with more
operator cases would recreate the fixed-shape matrix.

The binary literal bridge shows the reusable shape more clearly: it invokes a
left-child bridge, quantifies the right-child bridge over the threaded frame
state, then applies the shared `binOp` worker.  Its current theorem fixes both
children to integer constants and one operator, but the proof structure points
directly to the generic relation: two child bridges plus a worker refinement,
with no new list-length matrix required.

`Monadic.twinAgrees_binOp` is the first worker refinement needed by that
generalization: `binOpM` lifts the shared `evalBinOp` result through exactly
the legacy `Run.liftRes`, with no extra arithmetic semantics.  Heap-aware
operators use the corresponding `twinAgrees_unaryOp`/`binOpH` equations, so a
generic binary expression theorem can factor worker behavior from child
evaluation instead of duplicating operator cases.

The existing list theorem cannot specialize directly to a binary node: it
relates `evalOpenList`/`evalExprs`, while a binary expression has two child
evaluations followed by `binOpHM` and possibly a heap update.  The correct
generic theorem must expose that two-child sequencing explicitly; treating a
binary node as a synthetic expression list would be a deep rewrite and would
lose the node's own semantics.

The smallest state-threaded binary theorem is already represented by
`Monadic.twinAgrees_binOpHM_intBitAnd` and `Monadic.twinAgrees_binOpHM_intMult`:
they read the current heap, apply the shared heap-aware worker, and return the
updated frame state.  These equations are sufficient worker premises for a
generic two-child binary-node theorem; the remaining step is sequencing the
child bridges around them.

The literal binary proofs already abstract the right-child premise over every
threaded state, so their control skeleton can be generalized.  The remaining
restriction is the worker conclusion: replacing integer literals with arbitrary
child results requires a theorem relating `binOpHM op a b` to the legacy
heap-aware `evalBinOpH` result for all admitted operators and heap shapes.  The
existing worker equations cover only selected integer cases; adding more
literal proofs would not establish that parametric relation.

The worker definitions show why the domain cannot be widened by a blind
rewrite: `binOpHM` uses the monadic `listRepeatH` and `strFormatH` paths,
whereas the legacy `evalBinOpH` dispatches through `evalBinOpMultH` and its
heap-list helpers (and has a distinct string-modulo branch).  A generic worker
theorem therefore needs explicit refinement lemmas equating those shared
protocol workers on their admitted domains; outside those domains the theorem
must remain a loud refusal.

`Monadic.listRepeatH_eq_heapListRepeat` closes the first worker refinement
needed for that domain: the monadic list-repetition worker is definitionally
the same bounded `heapListRepeat` worker used by `evalBinOpH`.  The remaining
operator relation is dispatch and error-ordering around this shared worker,
not a second repetition algorithm.

The pinned differential row for `str_lab.fmt_mapping` (`%(k)s` over a heap
dict) agrees under CPython 3.9.25 and the monadic runner, but the worker paths
remain distinct: `strFormatH` adds heap-dict mapping traversal around the pure
`strFormat` worker.  A direct refinement theorem must therefore relate the
mapping walk and pure conversion results on the admitted dictionary domain;
the existing match is evidence for that domain, not a proof of the worker
equality.

No mapping-walk refinement theorem exists yet.  `strFormatMappingWalk` is a
fuel-bounded recursive traversal over heap entries; it calls
`strFormatDictFind` and `strFormatConv` at each token, while pure `strFormatWalk`
consumes a value list and a mapping flag.  The missing relation must preserve
key lookup, conversion order, accumulator text, and timeout/refusal outcomes;
replacing it with a value-only equality would erase the heap observation.

`Monadic.strFormatDictFind_eq_dictFind_string` closes the reusable key-lookup
leaf: for a string format key, the mapping walker’s string-key search is
exactly the ordinary `dictFind` search with `.str key`, including insertion
order and `keyEq` behavior.  The remaining mapping theorem is therefore the
fuel-bounded walk and conversion sequencing around this shared lookup.

`strFormatConv` is already the shared conversion worker called by both the
mapping walk and pure formatting paths.  Its scalar, `%c`, integer, and refusal
arms therefore need no duplicate refinement; the remaining relation is the
recursive walk's control and heap lookup around that worker.

`Monadic.strFormatMappingWalk_empty` closes the base case of that recursive
walk: an exhausted format-character list returns the accumulator for any heap,
address, and fuel.  The remaining prefix theorem must account for one token,
one fuel decrement, and the recursive continuation while preserving the
mapping lookup and conversion results.

`Monadic.strFormatMappingWalk_char_step` supplies the first prefix step for a
literal non-`%` character: one fuel unit is consumed and the accumulator gains
that character.  Special `%` prefixes remain separate semantic cases, so this
lemma is a safe structural induction seed rather than a rewrite of formatting
syntax.

`Monadic.strFormatMappingWalk_plain_prefix` composes that step for an arbitrary
list of literal characters.  Given a no-`%` invariant, induction on the list
consumes exactly one fuel unit per character and returns the accumulator
followed by `String.ofList` of the whole prefix.  This is the reusable
length-parametric composition needed by the walk proof; escaped-percent,
mapping-token, and conversion prefixes retain their own semantic branches.

`Monadic.strFormatMappingWalk_escaped_percent_prefix` gives the corresponding
length-parametric composition for any number of escaped-percent pairs.  Its
structural prefix contains two percent characters per repetition, consumes two
fuel units per pair, and appends one literal percent per pair.  The theorem is
separate from the literal-prefix result because `%` changes the walk's parser
branch, while heap lookup and conversion tokens remain independent cases.

`Monadic.strFormatMappingWalk_plain_prefix_append` is the continuation form of
the literal-prefix theorem: it accepts an arbitrary suffix after the safe
prefix and rewrites directly to the same walk on that suffix, with the prefix
text appended to the accumulator.  This exposes the exact fuel and accumulator
threading needed to compose mixed walks without enumerating prefix lengths.

`Monadic.strFormatMappingWalk_escaped_percent_prefix_append` supplies the same
continuation shape for an arbitrary run of escaped-percent pairs.  Each pair is
consumed by the existing `%%` branch and contributes one literal percent to the
accumulator before the unchanged suffix walk; token lookup and conversion stay
outside this structural theorem.

`Monadic.strFormatMappingWalk_plain_then_token` composes a safe arbitrary
literal prefix directly with the existing mapping-token branch.  It preserves
the heap lookup, conversion, key-error, timeout, and refusal outcomes while
threading the prefix accumulator and fuel exactly once; the token parser is
still consumed through its own equation theorem.

`Monadic.strFormatMappingWalk_escaped_percent_then_token` provides the matching
composition for any run of escaped-percent pairs before a mapping token.  It
threads the literal percent output into the token branch and preserves all of
the same heap and conversion outcomes, using the existing continuation and
token theorems rather than another parser or fixed-count case.

`Monadic.strFormatMappingWalk_plain_then_escaped` combines the two structural
prefix forms: an arbitrary safe literal segment followed by any number of
escaped-percent pairs and then an arbitrary suffix.  The proof composes the
two continuation theorems, so mixed-prefix fuel and accumulator accounting is
parametric in both lengths and introduces no finite bridge matrix.

`Monadic.strFormatMappingWalk_escaped_then_plain` closes the reverse ordering:
escaped-percent pairs followed by an arbitrary safe literal segment and
suffix.  It uses the escaped continuation first and the literal continuation
second, preserving the same exact fuel and accumulator accounting in either
segment order.

`Monadic.strFormatMappingWalk_token_then_plain` composes a mapping token with
an arbitrary safe literal continuation.  After the token branch resolves its
heap lookup and conversion, the literal continuation theorem is applied only
to the successful conversion arm; key errors, exceptions, timeouts, and
refusals remain unchanged.  This keeps the token parser and walk semantics
single-source while exposing the next mixed recursion boundary.

`Monadic.strFormatMappingWalk_token_then_escaped` supplies the corresponding
continuation for arbitrary escaped-percent pairs.  The successful conversion
arm threads the converted text into the escaped continuation, while all other
token outcomes are preserved directly.  The theorem remains parametric in the
pair count and reuses the existing parser and walk equations.

`Monadic.strFormatMappingWalk_token_then_plain_then_escaped` combines both
continuation forms after a token: an arbitrary safe literal segment followed by
any number of escaped-percent pairs.  It is a single parametric bridge over
the mixed suffix, preserving every token outcome and avoiding a matrix of
specialized segment counts.

`Monadic.strFormatMappingWalk_plain_then_escaped_then_token` supplies the
matching prefix composition: a safe literal segment, escaped-percent pairs,
and then a mapping token.  It first consumes the two structural prefix
continuations and applies the token branch at the remaining fuel, preserving
all heap and conversion outcomes without re-parsing or fixed-count expansion.

`Monadic.strFormatMappingWalk_token_then_escaped_then_plain` closes the reverse
mixed suffix: a mapping token, escaped-percent pairs, and a safe literal
segment.  It applies the token result to the reverse structural continuation,
preserving all non-success outcomes and keeping both segment lengths
parametric.

`Monadic.strFormatMappingWalk_segment_chain` generalizes the structural prefix
composition to an arbitrary list of `(literal characters, escaped-pair count)`
segments.  Induction on the segment list composes the existing continuation
theorems and carries a single no-`%` invariant for every literal segment, so
fuel and accumulator accounting are length-parametric without fixed-count
matrices.

`Monadic.strFormatMappingWalk_segment_chain_then_token` integrates that
arbitrary chain with the mapping-token branch.  The chain is consumed first,
then the token lookup and conversion outcomes are preserved exactly, giving a
single parametric bridge for all admitted structural prefixes before a token.

`Monadic.strFormatMappingWalk_token_then_segment_chain` supplies the reverse
bridge: a token followed by an arbitrary segment chain.  Its successful
conversion arm invokes the chain theorem, while every other token outcome is
preserved directly, completing the general chain/token composition boundary.

`Monadic.strFormatMappingWalk_segment_chain_token_segment_chain` composes
arbitrary segment chains on both sides of one mapping token.  It preserves the
token's heap and conversion outcomes while carrying independent no-`%`
invariants and parametric costs for the two chains, closing the general
token-position composition without a finite matrix.

`Monadic.strFormatMappingWalk_escaped_percent_step` supplies the matching
escaped-percent step: one fuel unit is consumed and `"%%"` appends a literal
percent before continuing.  Mapping-token and conversion prefixes remain
separate because they observe the heap and may raise or refuse.

`Monadic.strFormatMappingWalk_incomplete_percent` closes the terminal `"%"`
case with the exact `ValueError "incomplete format"` outcome, independent of
heap, address, fuel, and accumulator.  This preserves the formatter's error
ordering as the prefix induction proceeds.

The mapping-token parser remains a separate boundary.  `strFormatMapToken`
uses a local accumulator recursion to collect arbitrary key characters before
the closing `)` and conversion character; its prefix relation must account for
that accumulator and list-association explicitly.  No vacuous wrapper or
fixed-length parser theorem was added while that relation is unproved.

Its local equation is the exact relation needed: for any accumulator `key`,
the `c :: rest` arm calls `go (key ++ [c]) rest`, and the closing arm returns
`String.ofList key`.  A general theorem must connect this accumulator growth to
`String.ofList key ++ String.ofList prefix`; that is ordinary parser induction,
but it is not definitionally available through the generated `where` equation.

An explicitly named helper attempt confirmed the remaining limitation: Lean's
generated equation does not expose the recursive call in the rewritten
`pre ++ [c]` shape, so the accumulator theorem needs a separately defined
proof-side recursion or an equation lemma for the local `go`.  The failed
attempt was reverted; the parser and semantics remain unchanged.

A proof-side copy of `go` would merely be a second parser and would violate the
approved-parser rule.  The admissible route is an equation theorem generated
from the existing definition (or a refactoring of the definition itself that
preserves its parser semantics); no mirrored helper is introduced here.

`Monadic.strFormatMapToken_go_append` is the admissible equation theorem from
the generated local recursion.  Under the explicit invariant that the key
prefix contains no closing parenthesis, it relates arbitrary accumulator and
suffix lists to the parsed `(key, conversion, rest)` result while preserving
`String.ofList` concatenation.  This exposes the parser's own equation without
introducing a second parser.

`Monadic.strFormatMapToken_append_of_safe` connects that equation directly to
the parser node consumed by `strFormatMappingWalk`: a safe suffix ending in
`)` and a conversion character parses to the expected key and tail.  The walk
can now consume this parser result without re-parsing or changing its own
token semantics.

`Monadic.strFormatMappingWalk_token_branch` now connects the parser result to
the walk's token branch.  It preserves the exact heap-dict lookup,
`strFormatConv` outcomes, key-error case, dangling-reference refusal, and
recursive continuation; no token text is re-parsed.

The conversion branch needs no separate wrapper: the token theorem already
matches every `strFormatConv` outcome (`ok` with recursive continuation,
exception, timeout, or refusal) and preserves the accumulator update.  Adding
a theorem that only re-matches that result would duplicate control structure
without adding a refinement fact.

`Monadic.twinAgrees_callIn_top_ret_of_statement_bridge` is the first
length-parametric returning-call bridge.  It combines the arbitrary-list
threshold relation with the no-global frame embedding and leaves the
statement-node bridge as its only premise.

`Monadic.twinAgrees_callIn_top_next_of_statement_bridge` supplies the matching
normal-flow bridge.  It uses the same threshold and frame embedding while
preserving the legacy body's threaded post-state through `RFlow.next`.

`Monadic.twinAgrees_callIn_recursive_next_of_statement_bridge` extends that
normal-flow result to nested calls.  The caller-depth and frame-full guards
remain explicit, and the legacy result is compared after the same
`leaveCallDepth` decrement used by `leaveCallM`.

`Monadic.twinAgrees_callIn_recursive_ret_of_statement_bridge` supplies the
matching nested returning-flow bridge.  It preserves the returned value while
threading the post-body world through the recursive depth decrement.

`Monadic.twinAgrees_callIn_recursive_exn_of_statement_bridge` supplies the
exceptional nested-flow bridge.  It transports the exception and retained
frame state through the same recursive unwind, without enumerating body
shapes.

`Monadic.twinAgrees_callIn_recursive_timeout_of_statement_bridge` completes
the nested timeout case.  Since timeout carries no post-body frame, the
bridge preserves the timeout observation while retaining the same no-global
and depth guards.

There is no analogous statement-only bridge for classified refusal.  The
legacy `Run.unsupported msg` projection erases the internal
`RefusalCause`/snapshot, while `callInM` must retain those fields to enter its
refusal transport.  A future refusal bridge therefore needs an explicit raw
monadic body premise (or a refinement theorem for that projection); deriving
it from `execStmts` alone would be unsound.

`Monadic.twinAgrees_callIn_top_body_ret` provides the generic return-flow
counterpart.  It accepts raw monadic and legacy body results and an explicit
world equality, then transports both through the normalized top-depth call
boundary without imposing a statement-shape enumeration.

`Monadic.twinAgrees_callIn_top_body_exn` provides the matching top-depth
exception-flow comparison, retaining the exception and requiring the same
explicit post-body world equality.

`Monadic.twinAgrees_callIn_recursive_body_ret` is the corresponding non-top
depth rule.  It keeps the caller's `callDepth` inequalities explicit and
checks the legacy `leaveCallDepth` decrement against the monadic
`leaveCallM` result.

`Monadic.twinAgrees_callIn_recursive_body_exn` supplies the same non-top-depth
normalization for exceptional body results, preserving the exception while
decrementing the retained world depth on both sides.

`Monadic.twinAgrees_callIn_recursive_body_timeout` closes the remaining
non-top-depth timeout transport.  A raw timeout carries no world, so both
interpreters leave the caller state untouched and return the same timeout.

`Monadic.twinAgrees_callIn_recursive_body_unsupported` closes the classified
refusal transport as well.  The refusal cause and snapshot stay internal to
the monadic layer; the public projection compares the shared refusal message.

`Monadic.twinAgrees_callIn_empty_body` supplies the call-plan base case for an
empty function body.  Both evaluators perform argument binding and frame
normalization, then fall through to `None` without consuming a body statement.

`Monadic.twinAgrees_execOpenList_of_threshold` adds the matching arbitrary-list
threshold form.  A uniform lower bound `base` is preserved as the legacy list
walker consumes one fuel level per recursive tail, so callers can supply
pointwise statement bridges only above that bound rather than expanding a
fixed-count matrix.

`Monadic.callInMono_succ_body_next_of_execStmt_each` closes the next composition
step: an existing pointwise monadic/trunk statement bridge plus an explicit
`execStmt` `.next` result now supplies the raw body premise and the public
successor result for arbitrary statement-list length.

`Monadic.twinAgrees_execStmt_pass` is the first concrete statement-node bridge;
the empty-body/pass base case `Monadic.callInMono_succ_pass_body` confirms the
public successor result without introducing a fixed-count assignment theorem.

`Monadic.twinAgrees_execStmt_expr_constant` adds the analogous expression-
statement bridge for a constant expression, with the explicit fuel threshold
needed by the legacy evaluator's child-expression step.

`Monadic.twinAgrees_execStmt_expr_of_evalOpen` generalizes that control step:
any expression whose `evalOpen`/`evalExpr` bridge is supplied at positive child
fuel automatically gets the corresponding expression-statement bridge.

`Monadic.twinAgrees_execStmt_expr_of_evalOpen_exact` exposes the same rule at
the enclosing statement's exact fuel: callers supply the child relation at
`fuel - 1`, and the theorem accounts for the statement step once.  This is the
fuel shape needed when the mutual continuation invariant is instantiated.

`Monadic.twinAgrees_execStmt_expr_unaryInt` supplies the next concrete instance
for a unary operator over an integer literal.  Its two-step threshold records
both the unary child evaluation and the enclosing expression-statement step;
the recursive continuation and richer expression cases remain open.

`Monadic.twinAgrees_execStmt_expr_intAdd` supplies the corresponding binary
integer-literal addition instance through the generic expression-statement
control rule.  The child list is handled by the existing left-to-right bridge;
no fixed-length body or assignment matrix is introduced.
