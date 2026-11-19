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

The old receipt and the post-push receipt share **325 old `passed` rows** that
are no longer MATCH. A wall label is an observation, not a cause, so those
rows are treated as regressions until they are replayed on fresh
parser-native envelopes or closed by a standard-mandated refusal. The
stable-name join, fresh replay, group split, row names, and history boundary
for each group are recorded in
[`docs/c-survey-drop-audit.md`](c-survey-drop-audit.md) and its machine-readable
[`docs/c-survey-drop-audit.json`](c-survey-drop-audit.json).

The current fresh replay recovers **189** rows. The remaining **136** rows
stop at 67 floating parser-bit refusals, 43 layout or aggregate-binding
refusals, 6 declaration-binding refusals, 19 effective-type UB refusals, and
1 bounds UB refusal. These are measured groups, not explanations: each group
has a bisect boundary and a named route in the audit artifact. The denominator
addition is tracked separately from the 325 shared rows.

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
with clang's `RecordLayout`/array facts carried in the envelope. The focused
differential harness now injects the pinned record-layout plugin and checks the
declaration-identity join on plain scalar records. The current
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

The focused battery now includes the C23 §6.5.1p7 character-type exception
with a parser-derived `unsigned char *` access to an `int` object. It matches
the pinned little-endian oracle, while the incompatible `short *` pun remains
a loud refusal with `MemFault.effectiveType` semantics reserved for the
future general aliasing model.

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

The accepted F2 storage contract is [c-f2-object-memory-design.md](c-f2-object-memory-design.md).

## F1 exit state

**F1 exit-state audit (2026-11-18).** `CType` is still an alias of `String`, and type fields, layout interfaces, effective-type metadata, and semantics helpers still perform string operations for qualification stripping, typedef resolution, array and pointer recognition, and record-tag lookup. Parser-native declaration and record identities now join object sizes, member offsets and extents, bit-field facts, flexible-array markers, and nested anonymous records, but the spelling fallback remains in `Torture.lean` and the evaluator still receives string types. Differential rows cover scalar struct padding, profiled `_Alignas`, forward-declared record size, anonymous struct and union objects, aggregate copy, designated union initialization, nested arrays and records, postfix-qualified pointers, fixed array members, signed and unsigned bit-fields, flexible-array size and scalar access, low-bit signed conversion, and subobject bounds, with refusal rows for packed and aligned records, flexible-array initializers, vectors, complex types, function pointers, and missing layouts. The parser-layout battery is 66/84 MATCH and the baseline battery is 57/84 MATCH. A general `_Alignas` rule and the replacement of spelling operations with one shared structured QualType representation remain open, so F1 is not released.

F1 is not released. `LeanModels/C/Ast.lean` still defines `abbrev CType :=
String`, and type fields, layout interfaces, and memory effective-type fields
still use that alias. String operations on types remain in `Ast.lean`,
`Torture.lean`, `C23/Expr.lean`, `C23/Stmt.lean`, and `C23/Memory.lean`,
including qualification stripping, array splitting, pointer suffix tests, and
record-tag extraction. The extractor carries parser-native record-layout
facts, but the evaluator still has spelling-based fallback code, so the D1
shared `QualType` representation and library-owned layout join are incomplete.
The differential rows currently cover scalar struct padding and `_Alignas`
through the layout-backed `record-attributes` case, forward-declared record size,
anonymous struct and union objects, aggregate copy, designated union
initialization, nested arrays, postfix-qualified pointers, and an array
subobject bounds refusal. The layout-backed battery now matches signed and
unsigned in-range bit-field assignments, a flexible-array-member size and
scalar access, a fixed array member, and the profiled low-bit conversion for
out-of-range signed bit-field assignments. It also covers a nested record member
whose parser-native size and alignment facts agree with the native run. The
survey also has refusal rows for packed and aligned records,
flexible-array initializers, and missing layouts for arrays, vectors, complex
types, and function pointers. There is no matching row yet
for a general `_Alignas` layout rule. F1 exits only after
these type operations are removed from the semantics and each layout rule is
decided by the parser-native library with differential coverage.

**F1 type-string gate audit (2026-11-19).** `tools/check_c_type_strings.py`
is now the repeatable gate for the five C type paths. Its self-test passes and
the live audit reports the remaining `CType := String` alias and 31 actual or
ambiguous type-spelling sites. It excludes clearly unrelated name and byte
buffer operations while retaining unknown receivers for review. The effective-type
access family now consumes Clang's structured character-type observation at
integer loads and stores, with legacy envelopes using a finite scalar spelling
table. Aggregate initialization now reads the parser-native union tag through
the layout interface. Enum scalar classification now refuses when the parser
has not supplied an enumeration observation. F1 remains open with 31 findings, including
qualification
stripping, typedef resolution, pointer and array recognition, and record-tag
lookup. No F2 store work starts until this checker reaches zero and the full
survey is at least 1326/2214 with no DIVERGE.

The bit-field storage family now uses parser-native declaration and recursive
`QualType` observations for record-member facts and pointee extent. When those
observations are absent, the evaluator refuses instead of peeling a pointer
spelling. Existing bit-field rows remain differential refusal rows without the
optional Clang structured-layout plugin.

The parser-native builtin family now has an explicit `CBuiltin` constructor in
the shared `QualType` representation. JSON ingestion maps Clang's builtin
observations to that constructor, while C integer and floating projections use
the constructor before retaining the legacy spelling fallback. This does not
reduce the checker count yet because the remaining fallback is still required
for older envelopes.

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
