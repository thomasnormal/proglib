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

Since the constant-evaluator series (package constants, constant functions,
typedef widths) the 54 rows of `walls-1125b`, `walls-1126`, `walls-1126c/W1`
and `walls-1126e` are marked `passes`: each case loads and its parameters,
localparams, declared widths and package constants agree with the parser's
values, and the generate-local values of W1 are the packet's. The four
`walls-1126e` rows expected a refusal "pending helper"; the helper is the
width-exact evaluator, so their expectation is now the exact value. The 11
rows of `walls-1126c/W2` and `walls-1126d` are unchanged.
