# S1 cast and conversion price

This price is a source census over the current C semantic paths after the
declaration and expression nodes gained parser-native `QualType` fields. It
does not claim a survey result or an oracle result.

| family | current references | replacement shape |
| --- | ---: | --- |
| integer classification | 38 `intTyOf`/`intTyOf?` references | consume `QualType` builtin and enumeration cases, with one loud absence for an unrepresented type |
| pointer and pointer-integer classification | 9 `isPtrType`/`isPtrIntType`/`compatiblePointerTypes` references | use `QualType.pointerObject`, `pointee`, and canonical declaration identity, then refuse when the node has no observation |
| floating and character conversion | 12 comparisons against type spellings such as `float`, `double`, and `char` | dispatch on `CBuiltin` from the carried type, preserving the C23 conversion cases |
| normalization and layout fallback | 69 `normalizeTy` references | move qualifier and typedef resolution to `QualType.resolveTypedefs`, then pass the resolved node type to load/store and layout operations |

The counts include declarations, semantic call sites, helper definitions and
proof-side references. Several references belong to the same migration seam.
The core seam is `Expr.intTyOf?`, `Expr.isPtrType`, `Expr.isPtrIntType`,
`Expr.compatiblePointerTypes`, `Expr.normalizeTy`, and the corresponding
initializer and builtin paths in `C23/Stmt`. The conversion cases are
parser-node cases, so no source spelling table is added as a bridge.

The current checker reports these named seams and type-spelling comparisons in
addition to the `CType` alias. The expected short-term result is a larger,
honest finding set until each conversion family consumes the node-carried
`QualType`.

An implementation trial changed `intTyOf?` to accept only `Option QualType`.
The capped `Expr` build exposed 27 direct callers across arithmetic, bit-field,
initializer, pointer-difference, and value-conversion paths. The trial was
discarded before commit because changing only the first conversion path would
leave the remaining callers on the spelling table. The family therefore needs
one coordinated signature migration with every caller in the same rebuilt
commit.

A second trial removed the spelling table and kept only parser-native integer
projection. It compiled the C targets after routing missing call-site facts to
loud refusals, but that fallback would discard existing integer, bit-field,
initializer, and conversion matches before the full survey could classify
them. It was discarded without a semantic commit. The remaining work must
thread the actual node or declaration `QualType` through those callers and
re-measure the full corpus before landing.

The literal subfamily has a complete node fact. Integer and character literal
evaluation now reads the expression's carried `QualType` through
`intTyOfNode`, and the memory-invariance proof covers both success and loud
absence. Other integer consumers remain on the larger coordinated migration
boundary.

The pointer subfamily has a narrower sound boundary. `pointerTypeOfNode`,
`pointerIntegerTypeOfNode`, and `compatiblePointerTypesNode` now consume the
target or source expression's carried `QualType` in pointer loads, stores, and
the pointer cast cases. A missing node fact refuses the pointer-integer or
compatible-pointer operation. The existing `CType` parameter remains for
diagnostic text and layout keys, while classification no longer depends on a
spelling fallback at these cast sites.

The floating conversion trial was stopped before landing. It threaded the
node-carried `QualType` through floating literals, integral-to-floating,
floating casts, and floating-to-integral conversions, but the expression
memory-invariance proof still opened the conversion branches after the node
helper had been unfolded. The remaining goals were `MemInvariant (floatCast
v "float")`, `MemInvariant (floatCast v "double")`, and
`MemInvariant (floatToIntNode v structured)`. No semantic change from this
trial is retained. The next attempt must preserve the node helper as the
proof head or provide one general branch lemma before changing the evaluator.

The remaining integer and normalization seam is declaration-driven rather than
expression-driven. `C23/Stmt.lean` has eight `intTyOf?` or `normalizeTy`
sites in zero initialization, aggregate initialization, string-array copying,
parameter stores, and builtin overflow helpers. Those callers receive a
declaration identity and often a structured type separately, so replacing the
spelling helper at only one site would make zero initialization and stores use
different widths. A coordinated migration must thread the declaration's
resolved `QualType` through all eight sites, remove `Layout.normalizeTy`, and
make absent observations refuse. No partial replacement is retained.

The floating cast trial remains blocked at the proof head. Replacing the
`float`/`double` destination spelling in `IntegralToFloating`, `FloatingCast`,
and `FloatingToIntegral` with node projections leaves `MemInvariant` goals
after the conversion helper is unfolded. The unresolved forms are
`MemInvariant (floatCast v "float")`, `MemInvariant (floatCast v "double")`,
and the node floating-to-integer computation. The trial was discarded without
semantic changes. A sound implementation needs a branch lemma that keeps the
node helper opaque through `memInvariant_core`.

Compound assignment has the same representation boundary in a different
form. Clang carries `computeLHSType` and `computeResultType` on the
`CompoundAssignOperator`, while the current AST constructor carries only one
node `QualType` for the assigned expression. The C23 rule needs all three
types, so replacing the two compute-type lookups with the destination type
would silently change usual arithmetic conversions. The complete migration
requires carrying both parser-native compute observations through `Ast`,
JSON, and every compound-assignment consumer before deleting the final
`normalizeTy`/`intTyOf` calls. No partial replacement is retained.
