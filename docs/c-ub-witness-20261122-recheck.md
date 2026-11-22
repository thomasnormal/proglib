# C UB witness recheck, 2026-11-22

The named UB rows from the 2026-11-20 lead note were rebuilt and run with pinned Clang 21.1.8 at `-O0` and with UBSan/ASan. Every native and sanitizer run exited 0 with no sanitizer diagnostic. The current evaluator emits a loud unsupported refusal for every row.

| row | native | sanitizer | evaluator |
| --- | --- | --- | --- |
| `20000113-1.c` | exit 0 | exit 0 | `unsupported: no bit-field layout for 'x2'` |
| `bf-sign-2.c` | exit 0 | exit 0 | `unsupported: bit-field width 31 for 'long'` |
| `bitfld-8.c` | exit 0 | exit 0 | `unsupported: no bit-field layout for 'left'` |
| `bitfld-9.c` | exit 0 | exit 0 | `unsupported: no bit-field layout for 'left'` |
| `pr108498-2.c` | exit 0 | exit 0 | `unsupported: zero initialization lacks parser-native QualType for 'struct U'` |
| `pr110166-1.c` | exit 0 | exit 0 | `unsupported: no bit-field layout for 't'` |
| `pr70566.c` | exit 0 | exit 0 | `unsupported: no bit-field layout for 'f1'` |
| `pr86844.c` | exit 0 | exit 0 | `unsupported: cannot initialize aggregate 'int[2]'` |

No clean-sanitizer UB verdict is claimed for this named set.
