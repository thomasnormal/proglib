# Declaration layout family, 2026-11-22

The parser-native declaration-layout change joins anonymous aggregate fields to the checked Clang record layout without consuming the layout slot twice. It carries the expression's structured member type into the layout lookup, so anonymous fields are selected by QualType identity. The evaluator now accepts Clang OffsetOfExpr nodes with a parser-provided constant byte offset. Pointer arithmetic on array subobjects remains a loud refusal because the current bound model cannot distinguish valid enclosing-array arithmetic from an invalid subobject escape.

The focused battery uses unchanged C1-C3 sources and Clang 21.1.8 at O0, O2 and sanitizer profile. Four anonymous-field rows and one offsetof row are MATCH. The four array-subobject rows remain refused. pr44468.c and c23-empty-init-5.c advance past OffsetOfExpr to existing effective-type and indeterminate-read refusals. No DIVERGE appears in the focused rows. The full survey baseline remains 1209/2214 MATCH with 0 DIVERGE because a fresh 2214-row replay was not run for this focused step.

The focused receipt is [docs/c-declaration-layout-20261122.json](c-declaration-layout-20261122.json).
