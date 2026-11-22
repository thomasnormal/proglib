# Pointer-bit-cast wall price, 2026-11-22

The current approved-plugin C1-C3 survey has 25 sole dynamic rows whose first refusal is `pointer bit-cast across incompatible effective types`. Each unchanged source was compiled and run with pinned Clang 21.1.8 at O0, O2, and UBSan/ASan.

| measurement | count |
| --- | ---: |
| sole rows | 25 |
| O0/O2 agree and sanitizer is clean | 24 |
| O0/O2 termination differs | 1 |

The 24 agreeing rows have no sanitizer UB diagnostic. `pr60003.c` is a native NONDET row: O0 exits 0 while O2 aborts in its `__builtin_setjmp`/`__builtin_longjmp` path; the sanitizer exits 0. No UB witness is claimed for this row.

| row | O0 | O2 | sanitizer | evidence |
| --- | ---: | ---: | ---: | --- |
| `00103.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `00170.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `00217.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `20060412-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `20080222-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `980223.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `991228-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `alias-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `enum-3.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `gcc/testsuite/gcc.dg/c23-tag-alias-4.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `mayalias-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `mayalias-2.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `mayalias-3.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr10352-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr28778.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr36343.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr41317.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr43987.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr60003.c` | 0 | -6 | 0 | `nondeterministic-native` |
| `pr79043.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr90025.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pta-field-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pta-field-2.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `struct-aliasing-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `zero-struct-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |

The 24 clean rows exercise incompatible scalar, enum, aggregate, and subobject pointer representations. Native cleanliness does not establish defined C behavior under effective-type or provenance rules, so the current loud refusal remains. `pr60003.c` is separately blocked by the native disagreement. The next implementation price is the effective-type/provenance family, not a default pointer reinterpretation.

Price: parser-native access-type evidence plus the S2 byte/provenance store. No evaluator change is justified by this measurement.
