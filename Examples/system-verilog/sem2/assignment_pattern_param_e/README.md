# Parameter-default assignment-pattern wall

This source-shaped parameter declaration uses IEEE 1800-2023 §10.9's
`'{default: 4'h0}` assignment pattern. Slang retains the parser-native
assignment-pattern node, while the symbolic envelope records the exact
`AssignmentPattern:default-point` refusal because the current parameter
constant tier has no source-shaped aggregate-pattern value. Canonical E refuses
at that boundary before evaluating `P ^ x`. Xcelium 24.03-s004 reports three
rows `0000`, `1010`, and `xxxx`; Icarus Verilog 13.0 refuses the faithful
parameter-default syntax, so no Icarus oracle result is claimed. No scalar
lowering or default-point value is claimed.
