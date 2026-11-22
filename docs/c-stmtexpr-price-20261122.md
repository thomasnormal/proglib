# StmtExpr wall price, 2026-11-22

The current approved-plugin C1-C3 survey has six sole dynamic rows whose first refusal is `StmtExpr`. Each unchanged source was compiled and run with pinned Clang 21.1.8 at O0, O2, and UBSan/ASan.

| measurement | count |
| --- | ---: |
| sole rows | 6 |
| O0/O2 agree and sanitizer is clean | 6 |

Every row has clean O0/O2 and sanitizer exits with no diagnostic. This is no UB evidence. The refusal is the GNU statement-expression AST and control-flow boundary.

| row | O0 | O2 | sanitizer | evidence |
| --- | ---: | ---: | ---: | --- |
| `20000703-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `20000917-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `20020206-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `20020320-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `930406-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `950906-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |

Native cleanliness does not establish the exact value and lifetime semantics of GNU statement expressions. The loud refusal remains until the parser-native StmtExpr node is modeled directly.

Price: one AST-native statement-expression execution rule with its scoped temporary lifetime.
