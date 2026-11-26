# Wide package-constant refusal regression

These two parser-native rows pin the soundness boundary for package constants
wider than 32 bits under IEEE 1800-2023 §§6.20.2, 11.6, and 11.8. The
ordinary loader refuses both source-shaped values with
`wide package constant requires width-exact evaluation` instead of truncating
them to 32 bits.

Xcelium 26.09-s001 reports `rec::P[63:32] = 7` and `rec::Q[63:32] = 7`.
Icarus Verilog 13.0 reports the same values for the unchanged sources.
The agreement file uses `#guard_msgs (drop error)` so the push gate verifies
that both rows remain loud until width-exact package evaluation lands.
