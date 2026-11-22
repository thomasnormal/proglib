# Nested case-label wall price, 2026-11-22

The current approved-plugin C1-C3 survey has three sole dynamic rows whose first refusal is `case label nested in a control statement`. Each unchanged source was compiled and run with pinned Clang 21.1.8 at O0, O2, and UBSan/ASan.

| evidence | rows |
| --- | ---: |
| `clean-no-ub-witness` | 2 |
| `oracle-no-result` | 1 |

`00051.c` and `00143.c` have clean native and sanitizer runs. `medce-1.c` has no native oracle result in the pinned standalone profile. No UB witness is claimed.

| row | O0 | O2 | sanitizer | evidence |
| --- | ---: | ---: | --- |
| `00051.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `00143.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `medce-1.c` | compile-failed | 0 | compile-failed | `oracle-no-result` |

The refusal remains the parser-native switch/case control-flow boundary. Native cleanliness does not establish the semantics of labels nested in another control statement.

Price: one direct AST case-label/control-flow rule under N3220 §6.8.4.
