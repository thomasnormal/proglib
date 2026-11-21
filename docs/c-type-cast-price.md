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
