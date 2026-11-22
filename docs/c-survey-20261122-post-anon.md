# C survey measurement after anonymous-member layout, 2026-11-22

The replay used envelopes generated with Clang 21.1.8 and the string-byte, floating-bits, record-layout, and structured-type plugins. It ran the 2,214-row manifest with one million fuel per file, a 90-second wall per file, four child runners, one Lean thread each, and the lane scratch directory for temporary files.

The replay reports **1089 MATCH / 2,214 manifest rows**, with 2115 active rows after 99 no-entry-point rows. Counts are 1089 passed, 0 failed, 3 oracle/compiler rows, 24 libc refusals, 82 UB refusals, 578 unsupported refusals, 5 timeouts, 1 not-ingested rows, and 432 frontend rejections. The model replay reported zero failed rows.

The replay confirms the 1,089 MATCH result from the anonymous-member family. The seven-row increase from the 1,082 array-initialization replay is already recorded in `docs/c-anon-member-layout-20261122.md`. This measurement adds no semantic flip.

The S1 gate remains open at 1,326 MATCH / 2,214, with zero type-string operations, zero legacy `CType` aliases, zero DIVERGE, and zero unwitnessed UB verdicts. This replay did not rerun the native oracle or verify the 82 UB refusals.

## Highest sole static walls

| wall | sole | present |
| --- | ---: | ---: |
| `type-layout` | 344 | 1004 |
| `libc-call: __builtin_abort` | 146 | 348 |
| `libc-call` | 4 | 17 |
| `cast:IntegralToPointer` | 3 | 26 |
| `unsequenced-effects` | 3 | 17 |
| `cast:PointerToIntegral` | 2 | 25 |
| `libc-call: malloc` | 2 | 13 |
| `libc-call: __builtin_return_address` | 2 | 4 |
| `libc-call: memset` | 1 | 26 |
| `libc-call: __builtin_alloca` | 1 | 9 |

Measured commit: `cebadeb297e858121c85156a6bad341990540feb`
Measured at: `2026-11-22 06:05:58 UTC`
Manifest hash: `e384cfd4752ab5c621e0c8f1be56a6f10131bb19fcef7616c4e186a81ffc0d66`
