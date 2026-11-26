# Package and generate wall regression suite

This push-gate row table records every case in the current packets
`walls-1125b`, `walls-1126`, `walls-1126c/W1`, `walls-1126c/W2`,
`walls-1126d`, and `walls-1126e`. It has 65 rows. Each row names its
packet, expected construct-level outcome, and current outcome at the
2026-11-26 baseline. Rows currently failing are deliberately marked
`known-failing at 2026-11-26 pack baseline` so the suite remains green while
changes to the loader, extractor, or semantics cannot remove a case silently.
The source packets remain the differential authority for simulator values and
exact refusal text.
