# S1 loss account, corrected after deterministic replay

Old 1326 receipt `3cf3da8cc`; current deterministic receipt `f25b23fcd`. Current headline is 1275/2214 raw rows and 1275/2114 active rows.

| classification | rows |
| --- | ---: |
| regained | 67 |
| regression | 80 |
| correct refusal | 3 |
| instrument change | 8 |

Rows classified as regressions include missing structured QualType evidence, unsupported qualifiers, missing bit-field layout, partly initialized bit-field bytes, and the earlier parser/runtime losses retained by the prior audit. `pr19687.c` is the named correct refusal. Wall-clock kills in the current replay are runner errors, not fuel timeouts.

## Regression reasons

| reason | rows |
| --- | ---: |
| missing bit-field layout | 25 |
| partly initialized bit-field byte | 21 |
| pointer operation involving a string literal | 14 |
| integer-to-pointer conversion outside pointer type | 6 |
| nonValueRepresentation | 5 |
| unsupported qualifier | 3 |
| character-pointer subscript with long index requires an exact parser path | 2 |
| missing structured type | 1 |
| pointer bit-cast across incompatible effective types | 1 |
| non-null string initializer element exceeds the array extent | 1 |
| no size for pointee of 'char *' | 1 |

The full row detail, including the exact current refusal message, is in `docs/c-s1-loss-account-20261122.json`.
