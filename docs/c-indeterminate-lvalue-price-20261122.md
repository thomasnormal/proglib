# Indeterminate-lvalue wall price, 2026-11-22

The current approved-plugin C1-C3 survey has eight sole dynamic rows whose first refusal is `indeterminate lvalue read requires a representation choice`. Each unchanged source was compiled and run with pinned Clang 21.1.8 at O0, O2, and UBSan/ASan.

| evidence | rows |
| --- | ---: |
| `clean-no-ub-witness` | 7 |
| `sanitizer-witness` | 1 |

Seven rows have clean O0/O2 and sanitizer runs. `builtin-prefetch-2.c` has a sanitizer diagnostic and is the only qualified UB witness in this family.

| row | O0 | O2 | sanitizer | evidence |
| --- | ---: | ---: | ---: | --- |
| `20071120-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `20090113-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `20090527-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `20100430-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `builtin-prefetch-2.c` | 0 | 0 | 1 | `sanitizer-witness` |
| `pr101188.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr19687.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr33870-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |

The clean rows remain a representation-choice boundary for indeterminate lvalue reads. The loud refusal is retained until the memory semantics explicitly models the permitted representation choice.

Price: explicit indeterminate-byte and read-choice semantics. No clean native run justifies a fabricated value.
