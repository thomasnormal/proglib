# External object `b` wall price, 2026-11-22

The current approved-plugin C1-C3 survey has four sole dynamic rows whose first refusal is `extern object 'b' has no definition in the translation unit`. Each unchanged source was compiled and run with pinned Clang 21.1.8 at O0, O2, and UBSan/ASan.

| measurement | count |
| --- | ---: |
| sole rows | 4 |
| O0/O2 agree and sanitizer is clean | 4 |

Every row has clean O0/O2 and sanitizer exits with no diagnostic. This is no UB evidence. The refusal is the unresolved external-object/linkage boundary.

| row | O0 | O2 | sanitizer | evidence |
| --- | ---: | ---: | ---: | --- |
| `alias-2.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `alias-3.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `alias-4.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `gcc/testsuite/gcc.dg/c23-bool-2.c` | 0 | 0 | 0 | `clean-no-ub-witness` |

The rows exercise aliasing and C23 bool tests with an external object. Native cleanliness does not supply the missing companion definition, so the loud refusal remains.

Price: manifest-level companion closure and linked translation-unit ingestion, as for the `inside_main` family.
