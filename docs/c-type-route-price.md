# C structured-type route price

This is the F1 route decision for the shared C and C++ clang type layer. The
approved input remains clang's AST. No route parses a `qualType` string in
Lean or in the extractor.

The 2026-11-22 full survey has **344 sole `type-layout` rows** and 1,004
rows where the wall is present. The focused layout battery has already shown
that declaration identity joins are sound
for scalar, nested, anonymous, union, array-member, flexible-array and
bit-field layouts when the frontend observations are present. The remaining
wall is the absence of one structured type value passed from clang to the
envelope and then to the layout and memory libraries.

The same replay recorded 1,237 MATCH rows out of 2,214 manifest rows. The
layout wall is a measured front-end and envelope boundary. Its first
implementation price remains the recursive plugin projection below, with a
byte-identical double-run check and explicit leaves for unsupported Clang type
kinds.

## Candidate routes

| route | frontend fact | price and boundary | decision |
| --- | --- | --- | --- |
| Clang plugin projection | A pinned Clang AST plugin walks each `QualType` and emits one recursive tree with canonical declaration handles. The C++ `canonical_probe.cpp` already emits this shape for builtin, pointer, reference, qualified, function, record and enum types. | Lowest migration risk. It reuses the pinned plugin build and the existing declaration-id join. The C visitor must retain C arrays, typedef references, atomics, complex and vector types as named structured cases or explicit refusals. The plugin output gets a double-run byte-identical check. | **Selected** |
| libclang type/layout API | The extractor calls the pinned libclang API and serializes the same recursive tree and declaration handles. | It avoids a second AST plugin, but requires a stable C API wrapper for the exact pinned package and a separate lifetime/error boundary. The current lane has no such wrapper, so this adds an integration layer before the first row can be measured. | Rejected for this slice |
| declaration ids plus layout dump | Keep the existing AST type spelling and use declaration ids only for records and objects. | It handles record identity and sizes, but cannot represent scalar qualifiers, pointers, arrays, function types or typedef references without interpreting the spelling. It therefore leaves the 358 sole type walls and violates the shared structured-type requirement. | Rejected |

## Selected interface

The shared value is `LeanModels.Clang.QualType`. C adds the C-only scalar and
aggregate constructors in the same module, while C++ keeps its existing
constructors. Record and enum references carry the parser's canonical
declaration handle. An unsupported clang type is an explicit envelope leaf
with the clang kind, and the evaluator refuses it before allocating or
reading bytes. Layout facts remain separate parser observations keyed by
declaration identity.

The first implementation step is a C visitor in the existing pinned plugin
family. It emits type rows keyed by AST declaration identity, checks that
record and enum handles occur in the declaration table, and is byte-identical
across two runs. The extractor joins rows by declaration identity, never by a
type spelling. The next slice changes the envelope and `Ast.lean` together,
then removes one string operation family at a time from `Torture.lean`,
`C23/Expr.lean`, `C23/Stmt.lean` and `C23/Memory.lean`.

This price deliberately precedes F2 implementation. The object store can use
the structured type as its key, while C effective-type compatibility and the
Rust alias-model parameter remain semantic layers over that same key.
