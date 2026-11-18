# Parameter-default assignment-pattern wall

This source-shaped parameter declaration uses IEEE 1800-2023 §10.9's
`'{default: 4'h0}` assignment pattern. Slang retains the parser-native
assignment-pattern node and the fixed packed-array value is lowered to a
source-shaped four-element concat. Canonical E evaluates the default parameter
and returns `0000`, `1010`, and `xxxx` for the three source inputs. Xcelium
24.03-s004 reports the same three rows. Icarus Verilog 13.0 refuses the
faithful parameter-default syntax, so no Icarus oracle result is claimed. The
symbolic tier still refuses parameter-dependent packed widths at the
default-point boundary.
