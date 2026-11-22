# Timeout wall price, 2026-11-22

The current approved-plugin C1-C3 survey has 84 sole timeout rows. This receipt keeps the Lean timeout verdicts unchanged and qualifies the unchanged sources with bounded native O0, O2, and UBSan/ASan runs.

| native qualification | rows |
| --- | ---: |
| `clean-native` | 79 |
| `nondeterministic-native` | 2 |
| `sanitizer-witness` | 3 |

Seventy-nine rows have clean native O0/O2/sanitizer runs despite the model timeout. Three rows have sanitizer diagnostics: `arith-rand-ll.c`, `arith-rand.c`, and `shiftdi-2.c`. Two rows, `fprintf-chk-1.c` and `printf-chk-1.c`, disagree between native profiles. Native qualification does not establish a Lean termination bound.

| row | model first detail | native qualification |
| --- | --- | --- |
| `00040.c` | `per-file wall timeout (60s)` | `clean-native` |
| `00041.c` | `` | `clean-native` |
| `00128.c` | `` | `clean-native` |
| `20000412-2.c` | `` | `clean-native` |
| `20000605-1.c` | `` | `clean-native` |
| `20011008-3.c` | `` | `clean-native` |
| `20020108-1.c` | `` | `clean-native` |
| `20030916-1.c` | `` | `clean-native` |
| `20040313-1.c` | `` | `clean-native` |
| `20050224-1.c` | `` | `clean-native` |
| `20060905-1.c` | `` | `clean-native` |
| `20071030-1.c` | `` | `clean-native` |
| `20081218-1.c` | `` | `clean-native` |
| `951204-1.c` | `` | `clean-native` |
| `960521-1.c` | `` | `clean-native` |
| `961017-1.c` | `` | `clean-native` |
| `961017-2.c` | `` | `clean-native` |
| `980602-1.c` | `` | `clean-native` |
| `990513-1.c` | `` | `clean-native` |
| `991201-1.c` | `` | `clean-native` |
| `arith-rand-ll.c` | `` | `sanitizer-witness` |
| `arith-rand.c` | `` | `sanitizer-witness` |
| `ashldi-1.c` | `` | `clean-native` |
| `ashrdi-1.c` | `` | `clean-native` |
| `builtin-bitops-1.c` | `` | `clean-native` |
| `divcmp-1.c` | `` | `clean-native` |
| `divcmp-3.c` | `` | `clean-native` |
| `doloop-1.c` | `` | `clean-native` |
| `doloop-2.c` | `` | `clean-native` |
| `fprintf-chk-1.c` | `` | `nondeterministic-native` |
| `ieee/20001122-1.c` | `` | `clean-native` |
| `ieee/compare-fp-4.c` | `` | `clean-native` |
| `loop-11.c` | `` | `clean-native` |
| `loop-ivopts-2.c` | `` | `clean-native` |
| `lshrdi-1.c` | `` | `clean-native` |
| `memcpy-1.c` | `` | `clean-native` |
| `memcpy-2.c` | `` | `clean-native` |
| `memcpy-bi.c` | `` | `clean-native` |
| `memset-1.c` | `` | `clean-native` |
| `minmaxcmp-1.c` | `per-file wall timeout (60s)` | `clean-native` |
| `multi-ix.c` | `` | `clean-native` |
| `nestfunc-4.c` | `` | `clean-native` |
| `pr107881-1.c` | `` | `clean-native` |
| `pr110252-1.c` | `` | `clean-native` |
| `pr123978.c` | `` | `clean-native` |
| `pr19005.c` | `` | `clean-native` |
| `pr27260.c` | `` | `clean-native` |
| `pr28982a.c` | `` | `clean-native` |
| `pr28982b.c` | `` | `clean-native` |
| `pr37573.c` | `` | `clean-native` |
| `pr42512.c` | `` | `clean-native` |
| `pr43784.c` | `` | `clean-native` |
| `pr45034.c` | `` | `clean-native` |
| `pr47337.c` | `` | `clean-native` |
| `pr48571-1.c` | `` | `clean-native` |
| `pr49886.c` | `` | `clean-native` |
| `pr61725.c` | `` | `clean-native` |
| `pr65401.c` | `` | `clean-native` |
| `pr65418-1.c` | `` | `clean-native` |
| `pr68506.c` | `` | `clean-native` |
| `pr68532.c` | `` | `clean-native` |
| `pr71083.c` | `` | `clean-native` |
| `pr78675.c` | `` | `clean-native` |
| `pr82387.c` | `` | `clean-native` |
| `pr85529-2.c` | `` | `clean-native` |
| `pr87290.c` | `` | `clean-native` |
| `pr88693.c` | `` | `clean-native` |
| `pr91137.c` | `` | `clean-native` |
| `pr92904.c` | `` | `clean-native` |
| `pr94734.c` | `` | `clean-native` |
| `pr95731.c` | `` | `clean-native` |
| `pr98736.c` | `` | `clean-native` |
| `printf-chk-1.c` | `` | `nondeterministic-native` |
| `shiftdi-2.c` | `` | `sanitizer-witness` |
| `split-path-1.c` | `` | `clean-native` |
| `ssad-run.c` | `` | `clean-native` |
| `strcmp-1.c` | `` | `clean-native` |
| `strcpy-1.c` | `` | `clean-native` |
| `strlen-1.c` | `` | `clean-native` |
| `strlen-3.c` | `` | `clean-native` |
| `strncmp-1.c` | `` | `clean-native` |
| `subcmp-1.c` | `per-file wall timeout (60s)` | `clean-native` |
| `switch-1.c` | `` | `clean-native` |
| `usad-run.c` | `` | `clean-native` |

The timeout family is fuel or evaluator-cost bounded. The clean native rows remain candidates for a fuel or interpreter optimization item, while the sanitizer and native-disagreement rows stay separate. No timeout row is promoted to MATCH by this price.

Price: identify the first common interpreter step for a bounded subset, then raise fuel or optimize the semantics only with differential rows. A full unbounded retry is not admissible.
