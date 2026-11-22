# setjmp wall price, 2026-11-22

The current approved-plugin C1-C3 survey has three sole dynamic rows whose first refusal is `libc-call: __builtin_setjmp`. Each unchanged source was compiled and run with pinned Clang 21.1.8 at O0, O2, and UBSan/ASan.

| evidence | rows |
| --- | ---: |
| `clean-no-ub-witness` | 2 |
| `native-nonzero-without-sanitizer-diagnostic` | 1 |

`pr64242.c` exits 0 at O0 and aborts at O2 and under sanitizer without a diagnostic. The other two rows have clean O0/O2/sanitizer runs. No UB witness is claimed for the aborting row.

| row | O0 | O2 | sanitizer | evidence |
| --- | ---: | ---: | --- |
| `built-in-setjmp.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr64242.c` | 0 | -6 | -6 | `nonzero-without-sanitizer-diagnostic` |
| `pr84521.c` | 0 | 0 | 0 | `clean-no-ub-witness` |

The refusal remains the exact setjmp/longjmp external-call boundary. Native profile disagreement is kept separate from UB and does not justify admitting the call.

Price: one external control-transfer semantics family with profile-stable differential rows.
