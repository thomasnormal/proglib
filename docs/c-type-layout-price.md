# C type-layout wall price

This report compares the envelope-derived candidate wall with the runner's first refusal.

- survey commit: `949be152c`
- survey measured at: `2026-11-22T11:30:00Z`
- static candidates: 1004 present, 344 sole
- observed declaration `no layout`: 4 (candidate overlap 4)
- observed declaration refusals without a static candidate: 0
- static candidates without an observed declaration refusal: 1000

| corpus | static present | static sole | observed declaration no-layout | overlap |
| --- | ---: | ---: | ---: | ---: |
| `c-testsuite/single-exec` | 122 | 41 | 0 | 0 |
| `gcc.c-torture/execute` | 856 | 295 | 3 | 3 |
| `gcc.c23-run` | 26 | 8 | 1 | 1 |

## Most frequent observed declaration refusals

| detail | files |
| --- | ---: |
| `no layout for declared type 'DB_LSN[1235]'` | 1 |
| `no layout for declared type 'struct CS'` | 1 |
| `no layout for declared type 'const struct Df[8]'` | 1 |
| `no layout for declared type 'struct product_iSfd_'` | 1 |

type-layout is a candidate wall, not a dynamic verdict: the static heuristic over-approximates the files that reach a missing layout and misses some declaration types. Price a tier from observed no-layout refusals, retaining the static ranking for discovery.
