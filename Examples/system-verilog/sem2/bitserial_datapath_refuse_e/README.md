# Bit-serial datapath parser boundary

The faithful datapath source contains a select of a parenthesized expression
inside a concatenation. Slang reports `InvalidSelectExpression` before
elaboration, so the ordinary route keeps the source loudly refused under
IEEE 1800-2023 §11.5.1. This is a parser/elaboration boundary, not a claim
about the separate symbolic clocked-tactic timeout repro.
