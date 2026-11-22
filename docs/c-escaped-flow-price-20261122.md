# Escaped-flow wall price, 2026-11-22

The current approved-plugin C1-C3 survey has four sole dynamic rows whose first refusal is `break, continue or goto escaped a function body`. Each unchanged source was compiled and run with pinned Clang 21.1.8 at O0, O2, and UBSan/ASan.

| measurement | count |
| --- | ---: |
| sole rows | 4 |
| O0/O2 agree and sanitizer is clean | 4 |

Every row has clean O0/O2 and sanitizer exits with no diagnostic. This is no UB evidence. The refusal is an evaluator control-flow escape boundary.

| row | O0 | O2 | sanitizer | evidence |
| --- | ---: | ---: | ---: | --- |
| `00199.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `00207.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `00213.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `20040704-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |

The clean rows do not justify accepting escaped control flow. The loud refusal remains until function-body control-flow semantics carry break, continue, and goto destinations directly.

Price: one flow-aware evaluator rule for escaped control-flow outcomes. No source rewrite is admissible.
