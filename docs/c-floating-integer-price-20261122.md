# Floating-to-integer wall price, 2026-11-22

The current approved-plugin C1-C3 survey has three sole dynamic rows whose first refusal is `floating value used as an integer`. Each unchanged source was compiled and run with pinned Clang 21.1.8 at O0, O2, and UBSan/ASan.

| measurement | count |
| --- | ---: |
| sole rows | 3 |
| O0/O2 agree and sanitizer is clean | 3 |

Every row has clean O0/O2 and sanitizer exits with no diagnostic. This is no UB evidence. The refusal is the missing exact floating-to-integer representation/conversion boundary.

| row | O0 | O2 | sanitizer | evidence |
| --- | ---: | ---: | ---: | --- |
| `20000731-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `20011217-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr92904.c` | 0 | 0 | 0 | `clean-no-ub-witness` |

The loud refusal remains until parser-native floating widths and exact conversion-range rules are available. Native cleanliness does not justify an integer result.

Price: one parser-native floating-to-integer conversion rule with range and UB cases.
