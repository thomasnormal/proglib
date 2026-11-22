# String-pointer wall price, 2026-11-22

The current approved-plugin C1-C3 survey has 19 sole dynamic rows whose first refusal is `pointer operation involving a string literal`. Each unchanged source was compiled and run with pinned Clang 21.1.8 at O0, O2, and UBSan/ASan.

| measurement | count |
| --- | ---: |
| sole rows | 19 |
| O0/O2 agree and sanitizer is clean | 19 |

Every row has clean O0/O2 and sanitizer exits with no diagnostic. This is no UB evidence. The refusal is the missing static string-object and pointer-provenance semantics.

| row | O0 | O2 | sanitizer | evidence |
| --- | ---: | ---: | ---: | --- |
| `00112.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `20000910-2.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `20010915-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `20011126-2.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `20021204-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `20030928-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `20050218-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `20100827-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `930429-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `961125-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `991227-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `memchr-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr116799.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr34415.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr53084.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `string-opt-17.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `string-opt-5.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `va-arg-10.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `va-arg-9.c` | 0 | 0 | 0 | `clean-no-ub-witness` |

The next semantic step must allocate parser-provided string-literal bytes with static lifetime and carry their provenance through pointer operations. Native cleanliness does not justify treating a string literal as an ordinary absent object or classifying these rows as UB.

Price: parser-native string bytes plus static-object and pointer-provenance cases. No UB arm is justified by this receipt.
