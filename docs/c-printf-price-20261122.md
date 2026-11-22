# printf wall price, 2026-11-22

The current approved-plugin C1-C3 survey has four sole dynamic rows whose first refusal is `printf: unsupported format`. Each unchanged source was compiled and run with pinned Clang 21.1.8 at O0, O2, and UBSan/ASan.

| measurement | count |
| --- | ---: |
| sole rows | 4 |
| O0/O2 agree and sanitizer is clean | 4 |

Every row has clean O0/O2 and sanitizer exits with no diagnostic. This is no UB evidence. The refusal is the currently unsupported printf format boundary.

| row | O0 | O2 | sanitizer | evidence |
| --- | ---: | ---: | ---: | --- |
| `00174.c` | 1 | 0 | 0 | `clean-no-ub-witness` |
| `00175.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `00195.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `00220.c` | 0 | 0 | 0 | `clean-no-ub-witness` |

The rows remain refused until the supported printf subset is extended from parser-provided format evidence. Native cleanliness does not justify accepting an unsupported conversion.

Price: one format-node family with exact N3220 §7.23.6.1 conversions and differential rows.
