# C survey measurement, 2026-11-21

The fresh approved-plugin replay used Clang 21.1.8 and the corrected structured QualType extractor at commit `532aa55c6`. It regenerated the 2,214-row manifest and ran the bounded batch runner.

The result is **466 MATCH / 2,214 manifest rows**, with 2,132 active rows after 82 no-entry-point rows. Counts are 466 passed, 1 failed, 1 oracle/compiler row, 6 libc refusals, 86 UB refusals, 316 unsupported refusals, 1 timeout, 372 not-ingested rows, 965 frontend rejections, and 82 no-entry-point rows.

Against the 1,326 MATCH receipt at `3cf3da8cc`, 459 still match. Among the former matches, 296 are current ingestion refusals, 396 are frontend rejections, 126 are unsupported refusals, 48 are UB refusals, and 1 failed. The 48 UB rows remain unclassified until sanitizer witnesses are checked.

The current frontend rejection count is 965, compared with 806 on the 2026-11-18 receipt. Current not-ingested rows are 372, compared with 229, accounting for the increase in rejected rows.

The S1 gate is not met. The structured-type family must continue with declaration, cast/conversion, member/layout, and sizeof/alignof cases, while the survey and UB-witness checks remain open.
