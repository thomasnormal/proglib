# ExprWithCleanups wall price, 2026-11-22

The current approved-plugin C1-C3 survey has three sole dynamic rows whose first refusal is `ExprWithCleanups`. Each unchanged source was compiled and run with pinned Clang 21.1.8 at O0, O2, and UBSan/ASan.

| measurement | count |
| --- | ---: |
| sole rows | 3 |
| O0/O2 agree and sanitizer is clean | 3 |

Every row has clean O0/O2 and sanitizer exits with no diagnostic. This is no UB evidence. The refusal is the C/C++ cleanup-expression AST boundary.

| row | O0 | O2 | sanitizer | evidence |
| --- | ---: | ---: | --- |
| `950628-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `gcc/testsuite/gcc.dg/c23-stdarg-9.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr30185.c` | 0 | 0 | 0 | `clean-no-ub-witness` |

Native cleanliness does not establish cleanup ordering or temporary-lifetime semantics. The loud refusal remains until the approved AST node is modeled directly.

Price: one AST-native ExprWithCleanups lifetime and cleanup-order family.
