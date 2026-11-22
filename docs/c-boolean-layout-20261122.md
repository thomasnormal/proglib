# C Boolean object extent

C23 §6.2.6.2 gives `bool` one value bit. On the pinned LP64 profile its object occupies one byte. Allocation previously divided the value width by eight and produced a zero-byte object. Scalar layout now uses the same byte extent as integer loads and stores, preserving the Boolean value range.

These unchanged GCC corpus rows previously reported out-of-bounds UB on a zero-byte object. The rebuilt model and pinned Clang 21.1.8 at `-O0`, `-O2` and with AddressSanitizer and UndefinedBehaviorSanitizer all exited zero and produced empty stdout. The sanitizer runs emitted no diagnostic.

| Corpus row | Model before | Differential verdict after |
| --- | --- | --- |
| `20010604-1.c` | Out-of-bounds UB | MATCH |
| `20031010-1.c` | Out-of-bounds UB | MATCH |
| `20050502-1.c` | Out-of-bounds UB | MATCH |
| `20141107-1.c` | Out-of-bounds UB | MATCH |
| `20230510-1.c` | Out-of-bounds UB | MATCH |
| `pr81555.c` | Out-of-bounds UB | MATCH |

The full model replay moved from 1,089 to 1,094 passes across 2,214 rows. `minmaxcmp-1.c` moved from a pass to the 90-second wall timeout. `pr107881-1.c` and `subcmp-1.c` moved from UB refusals to wall timeouts. The new replay has zero failed rows and 74 UB refusals. Of those refusals, 20 rows produced a sanitizer diagnostic, 46 ran cleanly with matching native outcomes, six lacked a comparable oracle build or run, and two differed between native optimization levels. The clean runs leave 46 open rows under the S1 divergence rule.
