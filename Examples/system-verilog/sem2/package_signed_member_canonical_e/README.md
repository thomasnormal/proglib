# Package-array member constant evaluation

This clean-room pair exercises an explicit size cast over a complete member of
a package-scoped packed-struct array. The unsigned member is admitted as the
same `PackageAggElem` value already used for direct package-array element
selects. A signed member remains a loud extractor refusal: silently treating a
signed member as an unsigned packed element would violate IEEE 1800-2023
§§6.11 and 6.24. The positive rows match the pinned Xcelium reference
simulator for `K=0` and `K=1`; the signed source is checked for the named
`ConversionExpression:Explicit` refusal.

The conservativity boundary is intentional: direct `PackageAggElem` nodes and
their canonical-E evaluator are unchanged; only an unsigned full-width member
is mapped to that existing node. No dynamic indexed-part-select widening is
included, so the signed-base and wide-base guards remain loud.
