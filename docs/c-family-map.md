# C feature families and architecture map

This map uses the authoritative post-push score receipt
(`20261117T104602Z-score.json`, measured 2026-11-17) as its measurement. It
reports 888 MATCH rows out of 2,214, with 1 failed row, 12 libc refusals,
66 UB refusals, 823 other unsupported rows, 73 timeouts, 350 parser rejects,
and one compiler-oracle row. The separate entry-point census records 99
no-entry-point files. The families below partition the first outcome of every
row; the wall counts are present/sole counts from the dynamic ranking, so a
file can appear in more than one static family before its first outcome is
known.

## Drop table: 1,211 → 888 MATCH

The old receipt (`docs/c-survey.md`, 1,211 MATCH out of 2,112 scored files)
and the post-push receipt (888 MATCH out of 2,214 files) were joined by the
stable manifest row name. The old receipt covers 2,112 rows, while the new
manifest adds 102 rows, so the denominator change is reported separately.
Among rows present in both receipts, **325 old `passed` rows** now have a
refusal or timeout. The table assigns every one of those rows to its new
first runtime wall. It explains the measurement change without claiming that
an old accidental MATCH was correct.

| cause in the new first wall | rows | evidence / route |
| --- | ---: | --- |
| H2 undefined-value refusals | 0 | H2 reclassified non-MATCH undefined-value cases; no old MATCH row first refused there |
| H4 fuel and fixed-wall change | 1 | `minmaxcmp-1.c` is now the fixed per-file timeout |
| H5 own-definition precedence | 0 | the full receipt predates the H5 landing; the focused `strlen` and `printf` rows now MATCH |
| denominator change | 0 old MATCH drops; +102 rows scored | the old denominator excluded 102 no-entry-point rows; the new receipt scores the 2,214-row manifest |
| structured layout and object binding | 128 | `no layout`, `unbound declaration`, and `unknown enum declaration`; F1/F2 route |
| floating parser-native bits | 69 | `floating literal lacks parser-native bits`; shared SoftFloat route after F1 |
| library and string behavior | 79 | `printf`, `sprintf`, `strcmp`, `strlen`, `strcpy`, and string-literal refusals; F6 route |
| calls and variadics | 23 | `more arguments than parameters`; calls/`va_list` route |
| UB, lifetime, and bounds | 11 | named `MemFault.outOfBounds` refusals; memory-model route |
| parser-node refusal | 5 | `DesignatedInitUpdateExpr`; node-level ingestion/semantics route |
| other named semantic walls | 9 | the remaining named first refusals, retained for their family routes |
| **total shared rows whose old MATCH is no longer MATCH** | **325** | stable-name join of the two receipts |

This is a measurement explanation, not permission to preserve a wrong old
answer: any row whose old MATCH was correct must return to MATCH or become a
standard-mandated loud refusal. The denominator and H2/H4/H5 rows are
instrument effects; the remaining rows are the semantic walls the family plan
already names.

## 1. Parser, dialect, and entry-point boundary

This family contains the 350 parser rejects (349 C23 rejects, 56 of those
accepted by the registered C17 fallback), plus the 99 no-entry-point rows.
The one mechanism is a parser-profile manifest: clang AST extraction, the
per-file C23/C17 mode, and an explicit entry-point classification. It exists
in `extractors/c/extract.py`, `harness/c_frontend_census.py`, and
`harness/c_survey.py`. What is missing is broader dialect coverage beyond the
registered C17 fallback. The old source-text and partial-AST fallbacks are
debt and must stay deleted. These rows become MATCH only after this family
and the relevant semantic family below are complete; parser acceptance alone
does not execute a program.

## 2. Object memory, declaration identity, and layout

This family covers records, unions, arrays, bit-fields, aggregates,
compound literals, `sizeof`, and parameter/object layout. The one mechanism
is a declaration-identity keyed object layout and byte-region memory model,
with clang's `RecordLayout`/array facts carried in the envelope. The current
pieces are `LeanModels/C/Torture.lean` (`observedRecordLayout?`, `layoutFor`),
`LeanModels/C/C23/Memory.lean`, and `Expr.loadAt`/`storeAt`; missing pieces
are complete anonymous/nested/vector/VLA/parameter layouts and aggregate
copy, initialization, and return semantics. Per-construct layout tables and
type-spelling lookup are debt this mechanism replaces. The survey shows
20 sole rows for `struct S`, 9 for `V`, 8 for `va_list`, 5 for complex
double, and many one-off layout walls; these rows require this family plus
pointer provenance and initializer semantics where applicable.

## 3. Scalar numeric and floating representation

This family covers floating literals, binary32/binary64 operations and
casts, long double, complex values, integer conversion, and numeric
implementation-defined boundaries. The one mechanism is a C value layer
backed by the shared width-parametric `LeanModels/SoftFloat/Binary` model,
with parser-native literal bits and explicit C23 range/rounding checks.
Today `LeanModels/C/C23/Expr.lean` has integer/pointer/aggregate values and
the shared SoftFloat library exists, but C has no floating `CVal` constructor,
literal conversion, or floating memory operations. The old per-row literal
refusals and any host-float shortcut are debt. The survey's largest numeric
wall is 117 parser-native floating-bit refusals in the bounded run (the
committed survey also records long-double and floating-cast walls). Floating
rows become MATCH only after this family and layout/memory are complete for
their operand types; long double and unpinned environments remain refusals.

## 4. Pointer provenance, effective type, and conversions

This family covers pointer arithmetic, pointer-to/from-integer round trips,
function pointers, effective-type bit casts, pointer-to-array stride, and
provenance-preserving copies. The one mechanism is a typed provenance graph
whose conversions are checked against the C profile; `Memory.resolve`,
`Expr.functionPointerBitCast`, and the existing pointer `CVal` are the
current pieces. Missing are general pointer identity for all declarations,
compatible function-pointer calls, and effective-type checks for every byte
access. The refuse-only integer/pointer branches and ad hoc bit-cast guards
are debt. Current ranking examples are 24 effective-type bit-cast rows, 14
pointer-to-integer rows, and 13 integer-to-pointer rows. A row needs this
family plus layout or calls when its pointer targets those mechanisms.

## 5. Evaluation order, control flow, and termination

This family covers sequencing, calls with effects, gotos, labels, computed
labels, statement expressions, switch continuations, loops, and fixed-fuel
timeouts. The one mechanism is a small-step control-flow machine carrying an
effect set and explicit terminal outcomes. `Expr.evalArgs`, the sequencing
checks in `Expr.lean`, and `Stmt.execStmt`/flow are the current pieces;
timeouts still arise from the fuel boundary, and GNU control-flow nodes are
mostly refusals. The duplicated operator-specific unsequenced checks and
function-body goto patches are debt. The committed ranking has 87 timeout
rows, 11 unsequenced-effect sole rows, 7 `AddrLabelExpr` rows, and 7
statement-expression rows. MATCH requires this family plus the called
function/library family; a timeout is never evidence of correctness.

## 6. Library functions and hosted externals

This family covers specified libc and compiler builtins, stdout, strings,
memory functions, allocation, file I/O, and unresolved external objects such
as `inside_main`. The one mechanism is a profile-indexed external-function
registry returning values, memory effects, stdout effects, or a terminal
outcome. Current implementations are the library branches in
`LeanModels/C/C23/Stmt.lean` (printf family, `va_list`, allocation) and the
external-name handling in `Expr.lean`; missing are the remaining clause-7.26
functions, file handles, allocation lifetime, and general external-object
linking. Individual `printf`, `strlen`, `strcpy`, `inside_main`, and stream
special cases are debt. The current ranking includes 40 `inside_main` rows,
21 libc refusals in the committed survey, and printf/string walls. MATCH
requires this family plus memory, calls, and (for variadics) the next family.

## 7. Calls, variadics, and ABI-free argument transport

This family covers default argument promotions, `va_list`, extra arguments,
function-pointer calls, and parameter binding without inventing an ABI. The
one mechanism is an abstract argument sequence and cursor, with compatibility
checked against parser-provided types. Current code is `Expr.evalArgs`, the
`va_start`/`va_arg` branches in `Expr.lean`, and parameter binding in
`Stmt.lean`; missing are complete promoted-type compatibility and aggregate
arguments. The `more arguments than parameters` and `va_list` special cases
are debt. The 34-row extra-argument wall and 8-row va_list wall become MATCH
only when this family, call control flow, and each argument's value family
are complete.

## 8. Undefined behavior and implementation-defined choices

This family is the sound refusal layer for UB, nondeterminism, sanitizer
disagreement, signed bit-field conversion, and native abort outcomes. The
one mechanism is a structured `MemFault`/`Loud` outcome plus an oracle
classifier that never turns UB into a value. Current definitions are in
`LeanModels/C/C23/Memory.lean`, `Expr.lean`, and `Torture.lean`; missing are
complete lifetime/effective-type checks and a uniform distinction between
all implementation-defined choices. The old signed-bit-field residue rule
and any optimizer-dependent acceptance are debt. The committed survey has
86 UB rows and 3 native-abort failed rows; these are not MATCH candidates
until the standard or pinned profile determines a defined result.

## 9. GNU extensions and instrumentation

This family contains computed labels, statement expressions, function
instrumentation, unusual predefined expressions, and other GNU-only nodes.
The one mechanism is explicit dialect/node capability metadata: accepted
nodes get a semantics case, all others produce a named refusal. The current
node-level refusals live in `Expr.lean` and `Stmt.lean`; missing are any
deliberately registered GNU semantics and an instrument model. Per-node
string guards and accidental partial ingestion are debt. Rows become MATCH
only when a dialect is explicitly admitted and the control-flow/memory
families it uses are complete; otherwise refusal is the correct result.

## 10. Survey, oracle, and proof architecture

This family covers the measurement itself: fixed fuel/walls, O0/O2/sanitizer
triplets, expected stdout, parser provenance, and future C proofs. The one
mechanism is the existing `tools/leanc` plus `tools/c_torture_batch.py`,
`harness/c_torture_score.py`, and `harness/c_survey.py`, with one canonical
runner. These are present and gated; missing are the owner-directed weekly
survey generator and the C proof surface after the architecture gate. The
old fixture-fed C++ pipeline and any per-row runner are debt. A survey MATCH
requires every semantic family used by the row, and an oracle disagreement
must remain visible rather than being whitelisted.

If this lane were started today, I would make the envelope declaration
identity and profile explicit first, then build one memory/layout/value
kernel, one effect-aware control-flow machine, and one external registry.
The current evaluator has useful pieces but spreads policy across
`Expr.lean`, `Stmt.lean`, `Memory.lean`, and `Torture.lean`; each new
construct therefore pays a proof and refusal cost repeatedly. The special
cases named above should become registrations or derived rules over those
three mechanisms. The survey remains measurement and regression evidence,
not the architecture order.

## Review corrections and authorised honesty work

The independent architecture review confirms F1 (structured parser types) as
the foundation, followed by F2 (object memory), then the evaluator decision
and sequencing/control-flow families. I agree with that order. The current
memory core is useful, but effective types are not actually checked and
layout still lives in the scorer; these are architectural gaps, not merely
missing individual walls. The static `type-layout` table is only a
conservative inventory; route selection uses the dynamic first-refusal table.

The owner's settled decisions refine this map. C and C++ must share one
structured clang `QualType` representation and one object store; the C++ type
plugin is the starting point (D1). The language profile is GNU17: C89-only
implicit-int/K&R/implicit-declaration programs leave the denominator under an
explicit `out-of-scope-c89` verdict (D2). A minimal kernel-reducible or
unfolding-lemma proof surface with a `CallsTo`-style judgment and three proved
examples follows F2 immediately (D3), before evaluator-shape/F3 work. The
confirmed order is H1--H5, this map, F1, F2, proof surface, evaluator shape/F3,
F6+F5, F4, with F7 on shared SoftFloat after F1 and F8 translation-unit
linking whenever it fits.

## F1 exit state

F1 is not released. `LeanModels/C/Ast.lean` still defines `abbrev CType :=
String`, and type fields, layout interfaces, and memory effective-type fields
still use that alias. String operations on types remain in `Ast.lean`,
`Torture.lean`, `C23/Expr.lean`, `C23/Stmt.lean`, and `C23/Memory.lean`,
including qualification stripping, array splitting, pointer suffix tests, and
record-tag extraction. The extractor carries parser-native record-layout
facts, but the evaluator still has spelling-based fallback code, so the D1
shared `QualType` representation and library-owned layout join are incomplete.
The differential rows currently cover scalar struct padding and `_Alignas`
through the refusing `record-attributes` case, forward-declared record size,
anonymous struct and union objects, aggregate copy, designated union
initialization, nested arrays, postfix-qualified pointers, and an array
subobject bounds refusal. The survey also has refusal rows for packed and
aligned records, bit-field conversion, flexible-array initializers, and
missing layouts for arrays, vectors, complex types, and function pointers.
There are no matching rows yet for a completed bit-field layout, flexible
array-member layout, or a general `_Alignas` layout rule. F1 exits only after
these type operations are removed from the semantics and each layout rule is
decided by the parser-native library with differential coverage.

The five authorised instrument-honesty actions are recorded here. H1 is
already implemented: `abort` and `__builtin_abort` terminate through the
`.aborted` outcome, and `scoreEnvelope` compares that outcome with the oracle
classification. H2 is landed in commit `4352f5cda`: undefined values used as
arithmetic, truth, pointer, or unknown operator operands now produce named
unsupported refusals citing C23 clauses instead of fabricated
`indetAutomatic 0 0` UB. H3 uses `dynamic_wall_ranking` (the first runtime
refusal) for route selection; the static wall table remains measurement only.
H4 is landed in the same commit's gate change: the full-survey default fuel
is one million, with the fixed per-file wall as the termination guard;
focused probes may still pass an explicit bound. H5 is landed in the call
handler (commits `c15ae3bab` and `2fc7e48f0`): declaration identity gives a
translation-unit definition precedence over the external registry, with
pinned-Clang rows for program-defined `strlen` and `printf`. Centralising the
remaining name-based library arms into a profile-indexed registry is still
architecture work; it must preserve that precedence rather than reintroduce
the bug.

The authoritative post-push survey is **888/2,214 MATCH**, one failed row,
823 unsupported, 66 UB, 73 timeout, 350 parser rejects, and one
compiler-oracle row; the separate entry-point census records 99 no-entry-point
rows. The three historical failed rows are canonical-runner refusals on
unbound declarations while pinned native runs abort; they are not model/native
value divergences. H1--H5 are instrument changes; the remaining registry
centralisation is an architecture item for the family plan.
