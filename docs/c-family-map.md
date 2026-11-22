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

**F1 exit-state audit (2026-11-21).** The legacy `CType` alias and its type-string operations have been deleted. Declaration and expression nodes require same-invocation parser-native `QualType` observations. Layout decisions use declaration identity, structured expression observations and parser-provided record facts. Missing observations refuse loudly. The live checker reports 0 type-string operations and 0 legacy aliases. The full registered differential battery and the corpus survey still require a fresh approved-plugin replay, so F1 is not released until the survey reaches at least 1326/2214 with 0 DIVERGE and no unwitnessed UB refusals.

F1 code prerequisites are complete. `CType` is deleted, modeled nodes require same-invocation structured QualType observations, and layout paths use declaration identity or parser-native expression observations. The checker reports zero type-string operations and zero legacy aliases. F1 release still requires the fresh approved-plugin survey threshold and UB-witness gate.

**F1 type-string gate audit (2026-11-21).** `tools/check_c_type_strings.py` passes its self-test and reports zero live operations and zero legacy aliases. No F2 store work starts until the full survey gate reaches at least 1326/2214 with no DIVERGE.

**Historical CType migration price (2026-11-19).** Replacing `CType := String` requires
one schema family. At the time of this price, AST fields received displayed `qualType` text while the approved structured probe was optional and declaration keyed. The transition therefore needs parser-carried `QualType` observations
for every type-bearing AST node, JSON ingestion of those observations, typed
`Expr` and `Decl` constructors, and layout/effective-type interfaces keyed by
the resulting tree or its declaration identity. Legacy envelopes without the
observation must refuse at ingestion or at the first type query. A raw-string
coercion would keep the semantic parser alive under another name and would
violate the parser-native boundary. The first wrapper experiment compiled the
AST and expression layers, then stopped at three heterogeneous legacy layout
joins in `Torture.lean`, before reaching the loader and evaluator call sites.
This historical price was superseded by the landed coordinated envelope, loader and layout migration. No F2 store work starts before the survey gate is complete.

**Focused differential receipt (2026-11-19).** The committed `harness/c_cases.json`
battery without optional probes reports 27 MATCH, 94 REFUSE, and 0 DIVERGE
against pinned Clang 21.1.8. The refusal rows name missing optional parser
observations for function-pointer layouts, floating literal bits, pointee
strides, and anonymous bit-field layouts. The receipt is a focused battery,
not a full corpus survey. The approved record-layout, structured-type, and
floating-bit probe sources are present in `extractors/c`; on the pinned
Clang development environment their deterministic plugin-backed focused
receipt is 10 MATCH, 3 REFUSE, and 0 DIVERGE for the rows requiring those
observations. The three refusals are explicit field-offset observation
boundaries in the current evaluator. The no-plugin receipt remains the default when those optional
binaries are unavailable. The rerunnable pinned C1 sample cache currently
contains the registered 300-file slice. A fresh batch run on 2026-11-19
reported 172 passed, 0 failed, 88 refused-unsupported, 9 refused-ub, 30
not-parsed, 1 oracle-tests-compiler, and 0 timeouts. This is a sample receipt,
not a replacement for the 2,214-row survey denominator.

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

The parser-native aggregate floating family now resolves typedef references
inside array element `QualType` observations before sizing and initialization.
Direct, qualified, and typedef-backed `double[2]` initializers each MATCH the
pinned Clang 21.1.8 run with the structured-type and floating-bit plugins, for
3 MATCH, 0 REFUSE, and 0 DIVERGE. Without those optional observations the same
three rows remain explicit refusals naming the missing declared array layout.
The change is confined to parser-carried recursive type resolution and keeps
the legacy spelling path out of the new rows.

The first F2 memory audit rows are now explicit. The pointer-address
difference row reaches the parser-layout path and refuses the changed integer
token before dereference. The null and non-null pointer-byte rows refuse the
current non-value representation path for character reads until the shared
byte model is replaced. Pinned Clang 21.1.8 accepts all three sources, and the
rows report no model/native DIVERGE: one layout-plugin REFUSE and two
structured-plugin REFUSE results. The rows remain registered as refusal walls
so a later byte/provenance implementation can measure the exact flips.

The structured expression observation now carries parser range and node-kind
identity in addition to the start offset. The pointer-byte character rows use
that disambiguated `ArraySubscriptExpr` observation to select the character
load path. Both null and non-null pointer-byte rows MATCH pinned Clang 21.1.8
with the structured-type plugin, 2 MATCH / 0 REFUSE / 0 DIVERGE. No-plugin
runs retain the explicit parser-observation refusal boundary.

The arbitrary integer-to-pointer F2 case is registered as a refusal row. A
literal address cast is accepted by pinned Clang only as a source of later
undefined behavior, while the current evaluator refuses before fabricating
provenance. The row reports REFUSE with and without the structured-type plugin,
so the future PNVI-ae-udi recovery implementation has a fixed wall to flip.

The current structured-expression join also exposed a wrong answer in the
unsigned conversion family. Multiple Clang expression nodes share one source
range, so selecting only by offset chose the inner cast type for an outer
conversion. The join now filters by parser range, node kind, and expected
QualType. The frozen `20000528-1.c` row MATCHes with and without structured
observations, closing that DIVERGE against pinned Clang 21.1.8.

The current-parser no-plugin rerun over the available external cache produced
356 MATCH, 0 DIVERGE, 802 unsupported refusals, 19 UB refusals, 1 libc
refusal, 1 oracle-tests-compiler row, 0 timeouts, and 1,035 not-parsed rows
out of the frozen 2,214-file denominator. The missing rows reflect the
external cache's partial C1/C3 source availability, so this receipt is a
rerunnable partial-cache measurement rather than a replacement for the
canonical full-survey headline.

A bounded rerun on 2026-11-20 consumed all 2,214 entries of the same current
parser manifest, but its cache contained envelopes without the current
extractor hash and no pinned source tree for refresh. The controller therefore
produced 1,647 `not-ingested` stale-envelope rows and 567 frontend
`not-parsed` rows, with 0 scored rows and 0 DIVERGE. This is an environmental
boundary, not a survey result, and the canonical C-MATCH headline remains
unchanged until a source-complete cache is available.

The repeated bounded rerun at the current head reached the same 2,214-row
boundary. Its measured `sole` ranking is `not-ingested: stale envelope
extractor hash` for 1,647 rows, followed by `not-parsed` for 567 rows. The
first wall's price is a pinned source tree and fresh extraction cache, which
are absent from this environment. No semantic family is ranked above that
instrument wall until the source-complete cache is restored.

The plugin receipt's bit-field wrong-answer cluster is now refusal-only. The
registered rows cover one compound bit-field assignment and three widths above
the supported exact path. They report named layout or width refusals against
pinned Clang 21.1.8 with no DIVERGE. The evaluator refuses compound assignment
to a bit-field and widths above eight bits until the shared read-modify-write
store is implemented.

The string-literal pointer family is now refusal-only for pointer arithmetic
and comparison. Three frozen rows covering direct string arithmetic, a helper
returning a string pointer, and a static pointer-array element report named
`pointer operation involving a string literal` refusals with the structured
plugin and no DIVERGE. String-object byte semantics remain a separate future
family.

The nested-array pointer family now refuses before returning a comparison
value when the parser carries a pointer-to-array shape. The frozen
`20080424-1.c` row reaches a named array-subobject refusal with the current
structured envelope, and the focused harness records the corresponding
out-of-bounds refusal when only expression observations are supplied. No
pointer-array DIVERGE remains in the exercised receipt.

The remaining switch/name receipt row `pr35800.c` is now registered as a
parser-native subscript refusal. Its unsupported name-table path reaches
`subscript base is not an array or pointer type` under the structured plugin,
with no DIVERGE against pinned Clang 21.1.8. Switch semantics remain a
separate construct family.

The complete nine-row plugin DIVERGE set from the current receipt has now
been replayed after the pointer, string, bit-field, and switch closures. All
nine rows report REFUSE with no DIVERGE. Two rows use the more specific parser
diagnostic surfaced by the current evaluator, so the harness expectations now
record the actual named refusal rather than a stale predicted wall.

The batch survey controller now relocates a parsed envelope to the manifest's
current cache root when a copied manifest contains an obsolete absolute path.
It refreshes that envelope from the pinned source before invoking Lean, and
its self-test covers the relocation case. This closes the stale-envelope
instrument wall that previously made a rerun report runner errors at
`memcpy-1.c` instead of a model verdict.

Fresh rerun receipt for the pinned C1 300-file sample on 2026-11-20, using the
repaired batch and relocated envelopes, is 91 scored MATCH, 0 DIVERGE, 172
unsupported refusals, 6 UB refusals, 30 frontend rejects, 1
`oracle-tests-compiler`, and 0 timeouts. The receipt was produced with the
current parser and runner at commit `398a31727`. It is a C1 sample measurement,
not the 2,214-file C1-C3 headline.

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

The first mechanical `CType` wrapper migration was priced and reverted. After
explicitly adapting `Ast.lean`, the compiler reached the shared expression
module and then exposed the next boundary in `Stmt.lean`: eight declaration,
member-offset, and bit-field calls still require raw `String` keys. The wrapper
cannot land soundly as a local alias replacement. No coercion façade was
retained, and the live checker remains at its single honest alias finding.

The first typed interface slice is now landed in the layout layer. Declaration
bit-field, flexible-member, and member-offset queries take `CType` keys
explicitly while field names remain `String`. The existing parser-native and
legacy layout tables keep the same semantics, but callers no longer erase the
type key to a raw string at these boundaries.

The field-extent helper now states the same boundary explicitly. Its member
name is a `String` key and its declared member type is a `CType` key, so a
future `CType` representation cannot silently change field-name lookup.

The next effective-type slice was priced and reverted on 2026-11-20. Carrying
parser-native `QualType` alongside the legacy effective-type spelling in `CObj`
requires updating allocation and `realloc` constructors plus the complete
allocation, placement, and object-resolution theorem family. The first
compile exposed those constructor and theorem boundaries before any evaluator
callsite could be migrated. No partial field was retained and the alias gate
remains at its single `CType := String` finding.

The remaining envelope migration scope is now counted from the AST itself.
`LeanModels/C/Ast.lean` has 21 expression constructor arms and 4 declaration
constructor arms carrying `CType`, in addition to the `TypeNode` and layout
tables. A sound replacement must carry parser-native type evidence through
those 25 arms and their JSON loader cases before the effective-type store can
drop its spelling key. This is the next schema family after the priced layout
and allocation boundaries.

The first declaration-only implementation trial was priced and reverted on
2026-11-20. Adding an optional `QualType` to the four declaration constructors
(`VarDecl`, `ParmVarDecl`, `FieldDecl`, and `TypedefDecl`) compiled through the
AST and JSON loader, then reached roughly thirty `Torture.lean` pattern-match
and bridge-fixture sites. The constructor arity change also touches statement
parameter guards and layout census joins. The metadata should therefore be
carried by a declaration-identity table on the envelope first, with AST
constructor changes deferred until all consumers can use the same lookup.

The envelope-side declaration lookup now requires exactly one structured row
for an identity. Missing or duplicate rows return no observation, so malformed
frontend evidence cannot silently select the first duplicate. `TypeBridgeTests`
covers one valid identity, a missing identity, and a duplicate identity.

The extractor now enforces the same uniqueness before JSON emission. A
duplicate declaration identity in the structured probe is a loud extraction
failure, and the extractor self-test covers duplicate and distinct identities.

The first structured effective-type storage slice is now wired. `Mem` keeps a
parser-native `QualType` table keyed by allocated `ObjId`, separate from the
legacy `CObj.effTy` spelling. Declaration, parameter, global, and static
allocations populate the table when a unique envelope observation exists.
Checked integer loads and stores use the structural compatibility predicate
when both access and effective types are present, while legacy envelopes keep
the existing spelling path. Allocation lookup and placement-preservation
guards cover the new side table.

Explicit-placement allocation now has structured variants with the same
identity and placement guarantees. `realloc` remains a separate lifetime
transition until the standard's effective-type transfer rule is recorded in
the shared store contract.

The first `realloc` transfer trial followed the F2 contract's rule that copied
bytes carry effective-type state into the fresh allocation. It exposed the
existing theorem family as the next boundary: old/new load and store lemmas,
placement preservation, and dead-pointer results all quantify over the fresh
`Mem` value. The trial was reverted without changing those statements. The
next implementation must add side-table preservation lemmas before changing
the evaluator transition.

The side-table preservation slice is now available independently. A fresh
`ObjId` can copy the old allocation's parser-native type observation, and the
copy preserves concrete placements. `TypeBridgeTests` exercises that transfer
without changing `realloc` itself.

The realloc transition now uses that copy operation for both ordinary and
explicit-placement reallocations. The existing old/new load, store, placement,
and dead-pointer theorem family remains unchanged and compiles with the new
side-table projection lemmas. The bridge test checks that the fresh pointer's
identity retains the copied parser-native type.

The side table now has an explicit `Nodup` identity invariant. Allocation and
fresh-object transfer require a new object identity before adding a structured
row, while byte, stdout, cursor, and placement operations preserve the
invariant. This keeps duplicate effective-type identities loud at the memory
boundary as well as in the envelope.

Structured allocation now exposes uniqueness lemmas under the explicit fresh
identity premise. Both indeterminate and zeroed allocation preserve the
side-table `Nodup` invariant before an evaluator state transition consumes
their returned object.

Lifetime termination and byte stores also preserve the same invariant. The
memory lemmas cover `kill` and successful `storeBytes` results, so representation
updates and tombstone transitions cannot duplicate or erase parser-native type
identity metadata.

The public `free` operation now has a corresponding `structuredTypesUnique`
preservation theorem. Its null no-op and successful tombstone branches both
retain the same identity table, so callers can compose the invariant through
the `Except` memory API.

Automatic-scope cleanup now has the same proof. `killFrom` preserves
`structuredTypesUnique` through every fold branch, including static-object
skips and missing-object cases.

The abstract `va_list` operations now preserve `structuredTypesUnique` on
successful results. `vaStart`, `vaCopy`, `vaEnd`, and `vaArg` update only the
cursor table, so parser-native effective-type identities remain unchanged
through variadic argument traversal.

Typed stores now expose the same successful-result preservation boundary. The
generic byte-store proof covers integer, floating, pointer, function-pointer,
and pointer-integer representations, while checked integer stores preserve the
side table across their effective-type check and object-byte update.

Both `realloc` variants now preserve the invariant on successful results under
the same fresh-identity premise used by structured allocation. The valid path
copies the old parser-native observation to the fresh object before killing the
old one, and the null-pointer path leaves the existing table unchanged.

Unstructured allocation wrappers now expose direct preservation lemmas as well.
`alloc`, `allocZeroed`, their explicit-placement variants, `malloc`, and
`calloc` modify object and placement state without adding a structured row, so
the uniqueness invariant is carried through each API entry point.

The structured explicit-placement variants now carry the same fresh-identity
premise as ordinary structured allocation. `allocAtStructured` and
`allocZeroedAtStructured` therefore preserve side-table uniqueness while their
placement update remains orthogonal to parser-native type identity.

The compound-literal registry has the same boundary. `rememberCompound` records
the parser span and object identity without touching structured effective-type
rows, and its lookup-preservation lemma keeps that separation explicit.

The F2 pointer audit now has three differential rows. Pointer-address
subtraction and integer-to-pointer exposure refuse before the missing layout or
exposure witness can fabricate a result. The pointer-byte row remains a defined
native operation, while the current tier refuses it when parser-native pointer
layout is unavailable instead of reporting a false byte-level UB.

Effective-type establishment now follows C17 §6.5p6 for allocated storage.
`storeIntChecked` records the access type on an allocation without a structured
declaration row, while declaration-backed objects continue to use the shared
parser-native side table. A bridge guard exercises the allocated-store path.

The storage boundary keeps explicit destination placement and pointer-byte
exposure as address-observing cases in the F2 design. Refusal-bearing `free`
and `realloc` results are not asserted equal under source-address renaming,
because their diagnostics retain the offending pointer representation.

Successful byte and checked-integer stores now expose direct structured-type
lookup-preservation lemmas. Their object-byte and legacy effective-type updates
cannot alter parser-native declaration rows, and the bridge guard checks this
projection on an allocated store.

Lifetime-ending operations now expose the same projection. `kill`, `killFrom`,
and successful `free` preserve every structured-type lookup while changing
object liveness or tombstones.

The remaining metadata-only projections are explicit as well. `emitStdout`
preserves every lookup, and `copyStructuredType` preserves all existing keys
away from its fresh destination while exposing the transferred key at that
destination.

The four abstract `va_list` operations now expose lookup equality on successful
results as well. Cursor updates cannot change parser-native effective-type
identity.

Unstructured allocation entry points now expose lookup equality too. Ordinary,
zeroed, and explicit-placement allocation, plus `malloc` and `calloc`, leave
the structured side table unchanged while extending object or placement state.

The pointwise placement lemmas are now packaged as `Mem.AddressIndependent`.
`addressIndependent_mem` covers resolution, byte and typed accesses, variadic
cursors, character, floating, and pointer representations. It also covers
pointer-producing `offsetPtr` and `subscript` through map-under-renaming
equations. Character loads remain placement-independent even when their stored
pointer-byte values observe the pointee representation. Refusal payloads for
relational comparisons, `free`, and `realloc` remain explicit exceptions. The
evaluator-level behavior-set theorem still consumes this memory contract.

Pointer equality and one-past boundary classification are now included as
literal placement-independent comparisons. Relational cross-object failures
remain outside this equality field because their refusal payloads retain the
offending pointer values. Same-object relational ordering is included under
its existing shared-provenance premise. Cross-object refusal payload renaming
remains an explicit evaluator-relation case.

Pointer-byte observation has its explicit exception theorem in
`Ptr.exposedAddress_address`. It records the selected placement as the only
address-dependent value used by character reads of pointer representations.

The representation-level rename is now explicit through
`Ptr.renameAddress`, `CByte.renameAddress`, `CVal.renameAddress`, and
`Mem.renameAddresses`. Provenance and structured type keys remain fixed while
stored pointer representations, cursor values, and concrete placements follow
the object-to-address map.

The function-pointer store accessor now has its explicit named
`storeFunction_address_irrel` proof, completing the contract's representation
store cases.

**Structured member focus receipt (2026-11-22).** The approved-plugin focus now
contains 42 MATCH rows and 3 named REFUSE rows across record, typedef, array,
flexible-member and parameter boundaries. No DIVERGE remains in this focus.
The full C1-C3 survey still needs a replay after the extractor and evaluator
changes before the F1 threshold is assessed.

**Indeterminate bit-field audit (2026-11-22).** Clang 21.1.8 at `-O0` and
`-O2`, plus the UBSan/ASan build, exited cleanly for `20000113-1.c`,
`bf-sign-2.c`, `bitfld-8.c`, `bitfld-9.c`, `pr108498-2.c`, `pr110166-1.c`,
`pr70566.c` and `pr86844.c`. The current model either matches or stops at the
named partly-initialized-bit-field wall on these unchanged sources. No
sanitizer witness supports classifying that wall as undefined behavior.

**Abort-wall price (2026-11-22).** The first 20 static `libc-call:
__builtin_abort` candidates all exit 0 under pinned Clang `-O0` and `-O2`; 19
sanitizer runs are clean and one reports a sanitizer diagnostic. The fresh
replay now lets `20080719-1.c` run to MATCH, so this static wall is no longer a
dynamic refusal cluster. Its source exercises static aggregate arrays, a
function return pointer and switch selection.

**External-object wall price (2026-11-22).** The fresh dynamic ranking has 39
sole rows refusing `extern object 'inside_main'` with no definition. The sample
is GCC's `builtins/lib` companion corpus, where these source files are linked
into separate driver tests and are not complete translation units. The current
single-envelope survey cannot claim their linked behavior. A valid next step
requires a manifest-level companion closure and one parser envelope for the
linked translation unit, not an evaluator default for the missing object. The
measured split and complete row list are in
[`docs/c-external-object-price-20261123.md`](c-external-object-price-20261123.md).

**Pointer-bit-cast wall price (2026-11-22).** The dynamic ranking has 25 sole
rows at `pointer bit-cast across incompatible effective types`. The complete
25-row replay has 24 O0/O2-agreeing rows with clean sanitizer runs. `pr60003.c`
is native NONDET because O0 exits 0 while O2 aborts in its setjmp/longjmp path.
No sanitizer UB witness was found. The row table is in
[`docs/c-pointer-bitcast-price-20261122.md`](c-pointer-bitcast-price-20261122.md)
and the machine receipt is in
[`docs/c-pointer-bitcast-price-20261122.json`](c-pointer-bitcast-price-20261122.json).
Native cleanliness does not establish defined C behavior for these cases. The
current loud refusal is therefore retained pending the effective-type and
pointer-provenance family.

**Partly initialized bit-field wall price (2026-11-22).** The dynamic ranking
has 23 sole rows at `partly initialized bit-field byte`. All 23 have clean
pinned Clang `-O0`/`-O2` and UBSan/ASan runs. This is no UB evidence. The
complete receipt is in
[`docs/c-bitfield-price-20261122.md`](c-bitfield-price-20261122.md), with the
machine rows in [`docs/c-bitfield-price-20261122.json`](c-bitfield-price-20261122.json).
The next rule must use the parser-provided bit-field storage span for the
read-modify-write byte operation.

**Bit-field record-layout wall price (2026-11-22).** The dynamic ranking has
11 sole rows refusing `no layout for bit-field record 'struct S'`. Nine rows
have clean pinned O0/O2 and UBSan/ASan runs. `20230630-2.c` and
`20230630-4.c` abort identically at all three native profiles without a
sanitizer diagnostic and remain compiler-only checks. The receipt is in
[`docs/c-bitfield-record-price-20261122.md`](c-bitfield-record-price-20261122.md),
with machine rows in
[`docs/c-bitfield-record-price-20261122.json`](c-bitfield-record-price-20261122.json).
The refusal remains until parser-provided record and bit-field layout facts
support a sound byte-span rule.

**Indeterminate-lvalue wall price (2026-11-22).** The dynamic ranking has
eight sole rows refusing `indeterminate lvalue read requires a representation
choice`. Seven rows have clean pinned O0/O2 and UBSan/ASan runs.
`builtin-prefetch-2.c` has the only sanitizer diagnostic. The receipt is in
[`docs/c-indeterminate-lvalue-price-20261122.md`](c-indeterminate-lvalue-price-20261122.md),
with machine rows in
[`docs/c-indeterminate-lvalue-price-20261122.json`](c-indeterminate-lvalue-price-20261122.json).
The clean rows retain the loud representation-choice refusal.

**String-pointer wall price (2026-11-22).** The dynamic ranking has 19 sole
rows refusing pointer operations involving string literals. Nine available C1
samples exit 0 at pinned Clang `-O0` and `-O2` with clean UBSan/ASan runs.
The complete 19-row replay has clean O0/O2 and sanitizer exits for every row.
The receipt is in
[`docs/c-string-pointer-price-20261122.md`](c-string-pointer-price-20261122.md)
with machine rows in
[`docs/c-string-pointer-price-20261122.json`](c-string-pointer-price-20261122.json).
String-literal storage and pointer provenance are therefore the next
self-contained evaluator boundary after the current layout and evidence
prices. Native cleanliness supplies no UB witness.

**String-literal pointer boundary (2026-11-22).** The smallest priced row,
`20000910-2.c`, uses two string literals as `char *` values passed through
`strchr`. The envelope carries decoded bytes and the model allocates static
objects for each literal. Pointer equality and arithmetic still refuse because
literal pooling and object identity are implementation choices. C's permitted
same-address and distinct-address resolutions must be represented before these
operations can be admitted universally.

**Non-value representation wall price (2026-11-22).** The dynamic ranking has
17 sole rows at `nonValueRepresentation`. The sample includes integerized
function pointers, masked object addresses, `alloca` alignment observations
and pointer-derived layout constants. The complete replay has 14 clean rows,
two sanitizer-witnessed UB rows, and one row without a native oracle because
`loop-2c.c` has an unresolved `f` definition. The receipt is in
[`docs/c-nonvalue-price-20261122.md`](c-nonvalue-price-20261122.md), with
machine rows in [`docs/c-nonvalue-price-20261122.json`](c-nonvalue-price-20261122.json).
The clean rows observe exposed addresses or representations the current
PNVI-ae contract deliberately leaves unresolved, so the named refusal is
retained until the S2 memory store supplies the exposure choice.

**Long-double literal wall price (2026-11-22).** The dynamic ranking has 14
sole rows at `long double floating literal`. These rows exercise profile-sized
`long double` constants and builtins, while the approved IEEE parser currently
models binary32 and binary64 only. All 14 rows have clean pinned O0/O2 and
UBSan/ASan runs. The receipt is in
[`docs/c-long-double-price-20261122.md`](c-long-double-price-20261122.md),
with machine rows in
[`docs/c-long-double-price-20261122.json`](c-long-double-price-20261122.json).
The loud refusal is therefore an exact profile boundary, not a native mismatch
or sanitizer-qualified UB result.

**Floating-cast wall price (2026-11-22).** The dynamic ranking has five sole
rows refusing `floating cast has incompatible source and destination`. All five
have clean pinned O0/O2 and UBSan/ASan runs. The receipt is in
[`docs/c-floating-cast-price-20261122.md`](c-floating-cast-price-20261122.md),
with machine rows in
[`docs/c-floating-cast-price-20261122.json`](c-floating-cast-price-20261122.json).
The refusal remains the exact parser-native source/destination representation
conversion boundary.

**Floating-to-integer wall price (2026-11-22).** The dynamic ranking has three
sole rows refusing `floating value used as an integer`. All three have clean
pinned O0/O2 and UBSan/ASan runs. The receipt is in
[`docs/c-floating-integer-price-20261122.md`](c-floating-integer-price-20261122.md),
with machine rows in
[`docs/c-floating-integer-price-20261122.json`](c-floating-integer-price-20261122.json).
The refusal remains the exact parser-native floating-to-integer conversion and
range boundary.

**Integer-to-pointer wall price (2026-11-22).** The dynamic ranking has 12
sole rows refusing `integer-to-pointer conversion outside pointer type`. The
rows are address arithmetic, pointer round-trips and builtin-prefetch cases.
All 12 have clean pinned O0/O2 and UBSan/ASan runs. The receipt is in
[`docs/c-integer-pointer-price-20261122.md`](c-integer-pointer-price-20261122.md),
with machine rows in
[`docs/c-integer-pointer-price-20261122.json`](c-integer-pointer-price-20261122.json).
Native cleanliness supplies no UB witness. The current PNVI-ae contract
requires an exposure flag and recovery choice for each integer-to-pointer
conversion, so these refusals remain the correct boundary until S2 supplies
that choice.

**Floating-store wall price (2026-11-22).** The dynamic ranking has 11 sole
rows refusing `floating store without a floating layout`. These rows use
parser-native float and double objects whose size or IEEE representation is not
attached to the destination declaration. The binary32/binary64 literal parser
already has exact bits, so the next self-contained slice is joining those bits
to declaration-backed stores without guessing a layout.

**Floating-store sample boundary (2026-11-22).** `20000605-1.c` carries
parser-native `float` QualTypes on the `RenderInfo.scaley` field and local
`step`/`error` declarations, plus a record layout and binary32 type facts.
The evaluator still reaches `floating store without a floating layout`, so the
remaining gap is the expression-to-declaration join at a field or local store,
not missing Clang bits or ABI size.

**Floating pointer-loop boundary (2026-11-22).** `pr28982a.c` is the
remaining floating-store sample after the compound-store fix. Its parser
facts include `float *[20]`, `float[20]`, `int[20]` and `float[80]` layouts.
The model reaches a pointer-loop out-of-bounds refusal while the pinned native
and sanitizer runs exit 0. The next fix must preserve pointer post-increment
bounds through the loop without weakening the object-bound rule.

**Pointer-loop bound finding (2026-11-23).** In `pr28982a.c`, object 4 is the
parser-backed `float[80]` allocation with size 320. For an `inc == 17` or
larger loop, the final post-increment forms an offset beyond the one-past
bound after the last dereference. The model's `outOfBounds` refusal therefore
follows C23 §6.5.6p8 even though Clang O0/O2 and UBSan/ASan exit 0. Native
cleanliness does not witness defined pointer formation here.

**UB audit controller boundary (2026-11-23).** The current all-row native
qualification run reaches `930529-1.c`, whose pinned `-O2` executable exceeds
the audit wall. The row must be recorded as a per-file timeout. The audit
controller must never wait indefinitely or treat a partial audit as evidence
for the remaining refused-UB rows.

**UB qualification receipt (2026-11-23).** The resumable controller completed
all 57 current refused-UB rows with a one-second execution wall. The receipt is
in [`docs/c-ub-qualification-20261123.json`](c-ub-qualification-20261123.json)
with its rendered table in
[`docs/c-ub-qualification-20261123.md`](c-ub-qualification-20261123.md).
Twenty-five rows have sanitizer diagnostics, 27 have clean sanitizer runs and
therefore no UB witness, and five have no native oracle result because Clang
could not link them. The `930529-1.c` O2 execution is recorded as a timeout.

**Timeout wall price (2026-11-22).** The fresh survey has 84 sole timeout
rows. Bounded native qualification finds 79 clean O0/O2/sanitizer rows, three
sanitizer-witnessed rows (`arith-rand-ll.c`, `arith-rand.c`, and `shiftdi-2.c`),
and two native disagreements (`fprintf-chk-1.c` and `printf-chk-1.c`). The
complete receipt is in
[`docs/c-timeout-price-20261122.md`](c-timeout-price-20261122.md), with
machine rows in
[`docs/c-timeout-price-20261122.json`](c-timeout-price-20261122.json).
Native qualification does not establish a Lean termination bound.

**AddrLabelExpr wall price (2026-11-22).** The dynamic ranking has seven sole
rows refusing `AddrLabelExpr`. All seven have clean pinned O0/O2 and UBSan/ASan
runs. The receipt is in
[`docs/c-addrlabel-price-20261122.md`](c-addrlabel-price-20261122.md), with
machine rows in
[`docs/c-addrlabel-price-20261122.json`](c-addrlabel-price-20261122.json).
The refusal remains the GNU labels-as-values and computed-goto representation
boundary.

**StmtExpr wall price (2026-11-22).** The dynamic ranking has six sole rows
refusing `StmtExpr`. All six have clean pinned O0/O2 and UBSan/ASan runs. The
receipt is in
[`docs/c-stmtexpr-price-20261122.md`](c-stmtexpr-price-20261122.md), with
machine rows in
[`docs/c-stmtexpr-price-20261122.json`](c-stmtexpr-price-20261122.json).
The refusal remains the GNU statement-expression value and temporary-lifetime
boundary.

**Escaped-flow wall price (2026-11-22).** The dynamic ranking has four sole
rows refusing `break, continue or goto escaped a function body`. All four have
clean pinned O0/O2 and UBSan/ASan runs. The receipt is in
[`docs/c-escaped-flow-price-20261122.md`](c-escaped-flow-price-20261122.md),
with machine rows in
[`docs/c-escaped-flow-price-20261122.json`](c-escaped-flow-price-20261122.json).
The refusal remains the flow-aware evaluator boundary.

**External object `b` wall price (2026-11-22).** The dynamic ranking has four
sole rows refusing `extern object 'b' has no definition in the translation
unit`. All four have clean pinned O0/O2 and UBSan/ASan runs. The receipt is in
[`docs/c-extern-b-price-20261122.md`](c-extern-b-price-20261122.md), with
machine rows in
[`docs/c-extern-b-price-20261122.json`](c-extern-b-price-20261122.json).
The refusal remains the unresolved external-object and companion-linkage
boundary.

**Field-layout wall price (2026-11-22).** The dynamic ranking has four sole
rows refusing `no layout for field ''`. All four have clean pinned O0/O2 and
UBSan/ASan runs. The receipt is in
[`docs/c-field-layout-price-20261122.md`](c-field-layout-price-20261122.md),
with machine rows in
[`docs/c-field-layout-price-20261122.json`](c-field-layout-price-20261122.json).
The refusal remains the anonymous-field declaration-identity and layout join
boundary.

**Array-subobject pointer wall price (2026-11-22).** The dynamic ranking has
four sole rows refusing `pointer operation on an array subobject`. Two rows
have clean pinned O0/O2 and UBSan/ASan runs. `strlen-4.c` reports an UBSan
out-of-bounds index. `va-arg-21.c` reports AddressSanitizer leak diagnostics,
which are recorded separately from UB. The receipt is in
[`docs/c-array-subobject-price-20261122.md`](c-array-subobject-price-20261122.md),
with machine rows in
[`docs/c-array-subobject-price-20261122.json`](c-array-subobject-price-20261122.json).
The refusal remains the parser-native subobject-boundary family.
