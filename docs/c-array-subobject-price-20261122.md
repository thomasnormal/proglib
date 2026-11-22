# Array-subobject pointer wall price, 2026-11-22

The current approved-plugin C1-C3 survey has four sole dynamic rows whose first refusal is `pointer operation on an array subobject`. Each unchanged source was compiled and run with pinned Clang 21.1.8 at O0, O2, and UBSan/ASan.

| evidence | rows |
| --- | ---: |
| `clean-no-ub-witness` | 2 |
| `sanitizer-diagnostic` | 2 |

`strlen-4.c` reports an out-of-bounds index under UBSan. `va-arg-21.c` reports AddressSanitizer leak diagnostics, which are lifetime diagnostics rather than a proven pointer-operation UB witness. The two remaining rows have clean native and sanitizer runs.

| row | O0 | O2 | sanitizer | evidence |
| --- | ---: | ---: | ---: | --- |
| `20080424-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr124358.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `strlen-4.c` | 0 | 0 | 1 | `sanitizer-diagnostic` |
| `va-arg-21.c` | 0 | 0 | 1 | `sanitizer-diagnostic` |

The clean rows retain the pointer/subobject-boundary refusal. The sanitizer diagnostics are recorded separately and do not justify a general array-subobject rule.

Price: parser-native subobject bounds and pointer operation semantics, with leak diagnostics kept outside UB classification.
