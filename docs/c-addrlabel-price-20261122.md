# AddrLabelExpr wall price, 2026-11-22

The current approved-plugin C1-C3 survey has seven sole dynamic rows whose first refusal is `AddrLabelExpr`. Each unchanged source was compiled and run with pinned Clang 21.1.8 at O0, O2, and UBSan/ASan.

| measurement | count |
| --- | ---: |
| sole rows | 7 |
| O0/O2 agree and sanitizer is clean | 7 |

Every row has clean O0/O2 and sanitizer exits with no diagnostic. This is no UB evidence. The refusal is the GNU computed-label representation boundary.

| row | O0 | O2 | sanitizer | evidence |
| --- | ---: | ---: | ---: | --- |
| `20040302-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `20041214-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `20071210-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `920501-4.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `920501-5.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `990208-1.c` | 0 | -6 | 0 | `clean-no-ub-witness` |
| `pr70460.c` | 0 | 0 | 0 | `clean-no-ub-witness` |

The rows exercise GNU labels-as-values and computed gotos. Native cleanliness does not establish a portable or exact label-address representation. The loud refusal remains until the approved AST node semantics and control-flow relation are implemented.

Price: one parser-native AddrLabelExpr/indirect-goto semantics family. No source rewrite is admissible.
