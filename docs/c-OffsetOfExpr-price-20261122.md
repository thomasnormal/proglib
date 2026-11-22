# OffsetOfExpr wall price, 2026-11-22

The current approved-plugin C1-C3 survey has three sole dynamic rows whose first refusal is `OffsetOfExpr`. Each unchanged source was compiled and run with pinned Clang 21.1.8 at O0, O2, and UBSan/ASan.

| measurement | count |
| --- | ---: |
| sole rows | 3 |
| O0/O2 agree and sanitizer is clean | 3 |

Every row has clean O0/O2 and sanitizer exits with no diagnostic. This is no UB evidence. The refusal is the parser-native offset-of-expression layout boundary.

| row | O0 | O2 | sanitizer | evidence |
| --- | ---: | ---: | --- |
| `gcc/testsuite/gcc.dg/c23-empty-init-5.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr30778.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr44468.c` | 0 | 0 | 0 | `clean-no-ub-witness` |

Native cleanliness does not justify computing a field offset from type spellings or a guessed layout. The loud refusal remains until the parser-native OffsetOfExpr and layout facts are modeled.

Price: one AST-native offset-of rule joined to parser-provided declaration layout.
