# Field-layout wall price, 2026-11-22

The current approved-plugin C1-C3 survey has four sole dynamic rows whose first refusal is `no layout for field ''`. Each unchanged source was compiled and run with pinned Clang 21.1.8 at O0, O2, and UBSan/ASan.

| measurement | count |
| --- | ---: |
| sole rows | 4 |
| O0/O2 agree and sanitizer is clean | 4 |

Every row has clean O0/O2 and sanitizer exits with no diagnostic. This is no UB evidence. The refusal is the parser-native anonymous-field layout boundary.

| row | O0 | O2 | sanitizer | evidence |
| --- | ---: | ---: | ---: | --- |
| `00046.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `00050.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `anon-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr87053.c` | 0 | 0 | 0 | `clean-no-ub-witness` |

The clean rows do not justify inventing a field identity or offset. The loud refusal remains until parser-provided anonymous-field declarations and layout facts are joined.

Price: declaration-identity and parser-native field-layout join. No spelling-based field identity is admissible.
