# Integer-to-pointer wall price, 2026-11-22

The current approved-plugin C1-C3 survey has 12 sole dynamic rows whose first refusal is `integer-to-pointer conversion outside pointer type`. Each unchanged source was compiled and run with pinned Clang 21.1.8 at O0, O2, and UBSan/ASan.

| measurement | count |
| --- | ---: |
| sole rows | 12 |
| O0/O2 agree and sanitizer is clean | 12 |

Every row has clean O0/O2 and sanitizer exits with no diagnostic. This is no UB evidence. The refusal is the PNVI-ae integer recovery and exposure boundary.

| row | O0 | O2 | sanitizer | evidence |
| --- | ---: | ---: | ---: | --- |
| `00214.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `20000622-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `20010329-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `20021010-2.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `20041112-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `20050125-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `960116-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `builtin-prefetch-6.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `loop-2e.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr103255.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr39233.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr86231.c` | 0 | 0 | 0 | `clean-no-ub-witness` |

The rows exercise integer round-trips, masked addresses and builtin-prefetch paths. Native cleanliness does not select an exposed-address recovery choice. The loud refusal remains until S2 provides the explicit PNVI-ae choice.

Price: integer-to-pointer recovery with an exposure flag and provenance-preserving address choice. No integer default is admissible.
