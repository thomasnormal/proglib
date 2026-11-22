# Bit-field record-layout wall price, 2026-11-22

The current approved-plugin C1-C3 survey has 11 sole dynamic rows whose first refusal is `no layout for bit-field record 'struct S'`. Each unchanged source was compiled and run with pinned Clang 21.1.8 at O0, O2, and UBSan/ASan.

| evidence | rows |
| --- | ---: |
| `clean-no-ub-witness` | 9 |
| `nonzero-without-sanitizer-diagnostic` | 2 |

Nine rows have clean O0/O2 and sanitizer runs. `20230630-2.c` and `20230630-4.c` abort identically at O0, O2, and sanitizer without a sanitizer diagnostic. They are compiler-feature checks already classified as oracle-tests-compiler, not UB evidence.

| row | O0 | O2 | sanitizer | evidence |
| --- | ---: | ---: | ---: | --- |
| `20230630-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `20230630-2.c` | -6 | -6 | -6 | `nonzero-without-sanitizer-diagnostic` |
| `20230630-3.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `20230630-4.c` | -6 | -6 | -6 | `nonzero-without-sanitizer-diagnostic` |
| `pr52979-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr52979-2.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr58984.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr65215-3.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr79737-1.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr89195.c` | 0 | 0 | 0 | `clean-no-ub-witness` |
| `pr97764.c` | 0 | 0 | 0 | `clean-no-ub-witness` |

The clean rows exercise scalar-storage-order and bit-field record layout. The loud refusal remains until parser-provided record and bit-field layout facts support a sound byte-span rule. No layout default is justified by native cleanliness.

Price: parser-native record layout and bit-field storage facts. No evaluator approximation is justified.
