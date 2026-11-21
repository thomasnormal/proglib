# C UB witness audit, 2026-11-21

The eight lead-requested rows were compiled with pinned Clang 21.1.8 at `-O0` and `-O2`, then with UBSan and ASan under `-O0 -fno-sanitize-recover=all`. Every row compiled at both optimization levels and the sanitizer run reported no UB diagnostic.

| row | O0 | O2 | sanitizer | model |
| --- | --- | --- | --- | --- |
| `20000113-1.c` | clean | clean | clean | `refused-ub effectiveType` |
| `bf-sign-2.c` | clean | clean | clean | `refused-ub outOfBounds` |
| `bitfld-8.c` | clean | clean | clean | frontend refusal |
| `bitfld-9.c` | clean | clean | clean | frontend refusal |
| `pr108498-2.c` | clean | clean | clean | frontend refusal |
| `pr110166-1.c` | clean | clean | clean | frontend refusal |
| `pr70566.c` | clean | clean | clean | frontend refusal |
| `pr86844.c` | clean | clean | clean | frontend refusal |

The two model UB verdicts are DIVERGE because the pinned sanitizer supplies no UB witness. The six frontend refusals have no model UB verdict. No clean-sanitizer row is counted as a correct UB refusal.
