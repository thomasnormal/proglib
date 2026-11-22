# Long-double literal wall price, 2026-11-22

The current approved-plugin C1-C3 survey has 14 sole dynamic rows whose first refusal is `long double floating literal`. Each unchanged source was compiled and run with pinned Clang 21.1.8 at O0, O2, and UBSan/ASan.

| measurement | count |
| --- | ---: |
| sole rows | 14 |
| O0/O2 agree and sanitizer is clean | 14 |

Every row has clean O0/O2 and sanitizer exits with no diagnostic. This is no UB evidence. The refusal is the profile boundary for parser-native long-double representation.

| row | O0 | O2 | sanitizer | evidence |
| --- | ---: | ---: | ---: | --- |
| `20030914-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `20040208-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `20080502-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `960405-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `gcc/testsuite/gcc.dg/c23-float-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `gcc/testsuite/gcc.dg/c23-float-12.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `ieee/20010226-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `ieee/inf-2.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `ieee/inf-3.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `ieee/pr36332.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr44942.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `stdarg-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `va-arg-5.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `va-arg-6.c` | 0 | 0 | 0 | `clean-no-ub-witness` |

The long-double rows exercise constants and variadic arguments whose representation is wider than the admitted binary32/binary64 parser facts. Native cleanliness does not establish an exact representation for this profile.

Price: parser-native long-double bits and width, followed by conversion and variadic compatibility rows. No approximation is justified by this receipt.
