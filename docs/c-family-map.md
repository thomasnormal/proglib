# C feature families and architecture map

This map uses the committed C survey (`docs/c-survey.json`, measured
2026-11-17) as its measurement. The survey has 1,211 MATCH rows out of
2,214, with 3 failed rows, 21 libc refusals, 86 UB refusals, 353 other
unsupported rows, 87 timeouts, 350 parser rejects, 102 no-entry-point rows,
and one compiler-oracle row. The families below partition the first outcome
of every row; the wall counts are present/sole counts from the dynamic
ranking, so a file can appear in more than one static family before its first
outcome is known.

## 1. Parser, dialect, and entry-point boundary

This family contains the 350 parser rejects (349 C23 rejects, 56 of those
accepted by the registered C17 fallback), plus the 102 no-entry-point rows.
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
