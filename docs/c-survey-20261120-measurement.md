# C survey measurement, 2026-11-20

This receipt records the full 2,214-row measurement required before S1. The pinned Clang is 21.1.8. Envelope regeneration used the string-byte, floating-bits, record-layout, and structured-type plugins. Rows whose current structured-type probe refused a `QualType` were refused at ingestion instead of reusing an older envelope.

The measured result is **625 MATCH / 2,214 manifest rows**. The active denominator after no-entry-point rows is 2,128. The complete verdict counts are 625 passed, 1 failed, 1,137 not-parsed at ingestion, 1 oracle/compiler row, 11 libc refusals, 80 UB refusals, 330 unsupported refusals, 29 timeouts, and 86 no-entry-point rows.

The receipt at commit `3cf3da8cc` had 1,326 MATCH / 2,214. Of its 1,326 matching names, 701 no longer match in this replay.

- 490 rows are **instrument changes**. Their current structured-type plugin refused a `QualType` or no current structured envelope was available. They are listed per row in [`measurement-report.json`](c-survey-20261120-measurement.json).
- 2 rows are **correct refusals**. The pinned sanitizer run reported undefined behavior, and the model refused. They are `pr44555.c` and `strlen-4.c`.
- 209 rows are **regressions**. Their pinned sanitizer run was clean, or the current run timed out or failed. The rows and first current refusal are listed in the JSON receipt.

The eight required wrong-answer checks had clean Clang O0, O2, and sanitizer runs. `20000113-1.c` failed in the model, `bf-sign-2.c` and `pr86844.c` refused UB, `pr108498-2.c` was an ingestion refusal, and `bitfld-8.c`, `bitfld-9.c`, `pr110166-1.c`, and `pr70566.c` matched. A clean sanitizer result makes a `refused-ub` verdict a DIVERGE. The full per-row classification is in the JSON receipt.

The 2026-11-18 receipt has 354 rejected/not-parsed rows. The 2026-11-19 current-parser receipt has 567, exactly 213 more. That increase is a manifest/instrument change before the final structured replay, not a semantic wall. The final structured-envelope receipt has 1,137 rejected/not-parsed rows because it requires the structured plugin and refuses 490 parsed names whose probe could not produce a current envelope. The same-day 2026-11-20 no-plugin receipt has 1,035 rejected/not-parsed rows.

The current `c-torture-run` rebuild was attempted under `MemoryMax=24G` and failed at `LeanModels/C/C23/Memory.lean:4365` on a `change` tactic. No current build pass is claimed. The survey used the existing runner binary timestamped 2026-11-20 20:07 UTC.
