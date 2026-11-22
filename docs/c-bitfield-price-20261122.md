# Partly initialized bit-field wall price, 2026-11-22

The current approved-plugin C1-C3 survey has 23 sole dynamic rows whose first refusal is `partly initialized bit-field byte`. Each unchanged source was compiled and run with pinned Clang 21.1.8 at O0, O2, and UBSan/ASan.

| measurement | count |
| --- | ---: |
| sole rows | 23 |
| O0/O2 agree and sanitizer is clean | 23 |

Every row has clean O0/O2 and sanitizer exits with no diagnostic. This is no UB evidence. The current refusal is the parser/layout boundary for partly initialized bit-field bytes, not a claimed undefined result.

| row | O0 | O2 | sanitizer | evidence |
| --- | ---: | ---: | ---: | --- |
| `20000113-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `20190901-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `921016-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `bitfld-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `bitfld-10.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `bitfld-8.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `bitfld-9.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `gcc/testsuite/gcc.dg/c23-tag-alias-7.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr108498-2.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr110165-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr110166-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr111613.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr31169.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr40493.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr60017.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr66556.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr70127.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr70566.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr78170.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr86659-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr86659-2.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr88739.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr98366.c` | 0 | 0 | 0 | `clean-no-ub-witness` |

The next semantic step must model the parser-provided bit-field storage span and read-modify-write bytes. It must not infer a value from Clang cleanliness or classify these rows as UB. The earlier eight named rows and the remaining 15 rows have the same qualification result.

Price: one parser-native bit-field byte-span rule and its differential rows. No UB arm is justified by this receipt.
