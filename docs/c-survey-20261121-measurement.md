# C survey measurement, 2026-11-21

The fresh approved-plugin replay used Clang 21.1.8, parser-native structured `QualType` observations, and the regenerated 2,214-row manifest. The bounded batch runner used one million fuel per file, a 90-second per-file wall timeout, four child runners, and `TMPDIR=/scratch/thomas-ahle/gate/ls-cpp/tmp`.

The result is **610 MATCH / 2,214 manifest rows**, with an active basis of 2,131 after 83 no-entry-point rows. Counts are 610 passed, 2 failed, 1 oracle/compiler row, 7 libc refusals, 55 UB refusals, 506 unsupported refusals, 2 timeouts, 78 not-ingested rows, and 953 frontend rejections. No DIVERGE verdict was reported.

Against the 1,326 MATCH receipt at `3cf3da8cc`, the current replay is lower by 716 MATCH rows. The receipt records the changed verdict classes and parser/instrument state for follow-up. This measurement is authoritative for the current S1 gate. The eight required clean-sanitizer witness rows have a separate receipt and none remains an unwitnessed clean-sanitizer UB verdict.

The largest dynamic wall is frontend rejection at 953 rows. The static structured-type wall is present in 667 rows and is sole in 344 rows. The S1 gate remains open until the structured-type family reaches at least 1,326 MATCH / 2,214, with zero type-string operations, zero `CType` aliases, zero DIVERGE, and zero unwitnessed UB verdicts.
