# Non-value representation wall price, 2026-11-22

The current approved-plugin C1-C3 survey has 17 sole dynamic rows whose first refusal is `nonValueRepresentation`. Each unchanged source was compiled and run with pinned Clang 21.1.8 at O0, O2, and UBSan/ASan.

| evidence | rows |
| --- | ---: |
| `clean-no-ub-witness` | 14 |
| `oracle-no-result` | 1 |
| `sanitizer-witness` | 2 |

Fourteen rows have clean O0/O2 and sanitizer runs. Two rows have sanitizer diagnostics, so they are qualified UB witnesses. `loop-2c.c` has no native oracle result because its standalone translation unit has an unresolved `f` definition.

| row | O0 | O2 | sanitizer | evidence |
| --- | ---: | ---: | ---: | --- |
| `20011121-1.c` | 0 | 0 | 1 | `sanitizer-witness` |
| `20050215-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `941014-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `941014-2.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `980526-2.c` | 0 | 0 | 1 | `sanitizer-witness` |
| `alloca-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `loop-2c.c` | compile-failed | 0 | compile-failed | `oracle-no-result` |
| `pr15296.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr17133.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr22098-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr22098-2.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr22098-3.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr23467.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr36339.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr38051.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr58209.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr97421-3.c` | 0 | 0 | 0 | `clean-no-ub-witness` |

`20011121-1.c` reports null member access while forming the `b` member address in a null struct pointer expression. `980526-2.c` reports signed left-shift overflow. The remaining clean rows exercise pointer/integer representation, alloca alignment, or pointer-derived constants without a sanitizer witness. The loud `nonValueRepresentation` refusal remains for those rows until the PNVI-ae exposure choice and S2 byte/provenance store are available.

Price: one exposure/provenance rule with explicit integer-pointer and pointer-byte choices. No default address token is admissible.
