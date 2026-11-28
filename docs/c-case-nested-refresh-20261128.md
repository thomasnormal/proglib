# Nested case-label focused refresh, 2026-11-28

This receipt refreshes the three unchanged C2/C1 rows whose committed survey
wall was `case label nested in a control statement`. Pinned Clang 21.1.8 was
run at O0, O2, and UBSan/ASan where the standalone source links. The model ran
the existing parser envelopes with one million fuel.

| row | model | O0 | O2 | sanitizer |
| --- | --- | --- | --- | --- |
| `00051.c` | MATCH, exit 0 | 0 | 0 | 0 |
| `00143.c` | REFUSE, `case label nested in a loop` | 0 | 0 | 0 |
| `medce-1.c` | MATCH, exit 0 | no oracle result | 0 | no oracle result |

The focused movement is `MATCH 0→2, DIVERGE 0→0`. `medce-1.c` cannot claim an
O0 or sanitizer oracle because its deliberate `link_error` symbol is unresolved
in the standalone profile. The full 2,214-row survey was not rerun.
