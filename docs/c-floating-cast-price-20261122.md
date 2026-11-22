# Floating-cast wall price, 2026-11-22

The current approved-plugin C1-C3 survey has five sole dynamic rows whose first refusal is `floating cast has incompatible source and destination`. Each unchanged source was compiled and run with pinned Clang 21.1.8 at O0, O2, and UBSan/ASan.

| measurement | count |
| --- | ---: |
| sole rows | 5 |
| O0/O2 agree and sanitizer is clean | 5 |

Every row has clean O0/O2 and sanitizer exits with no diagnostic. This is no UB evidence. The refusal is the missing exact source/destination floating representation conversion.

| row | O0 | O2 | sanitizer | evidence |
| --- | ---: | ---: | ---: | --- |
| `00204.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `20020413-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `990413-2.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `align-2.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `ieee/20011123-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |

The next implementation must use parser-provided floating widths and exact conversion semantics. Native cleanliness does not justify a binary64 approximation for an incompatible cast.

Price: one parser-native floating conversion rule with rows for both source and destination widths.
