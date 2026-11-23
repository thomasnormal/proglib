# Ibex SHA-2 digest packed-dimension boundary

The pinned SHA-2 source declares `digest_i` as a packed array of the package
typedef `sha_word64_t [7:0]`. Slang retains this source-shaped port. The
extractor now recovers the fixed typedef ranges from the parser-backed target
syntax, preserving both `[7:0]` and `[63:0]` in the envelope. The ordinary
loader moves past `decl 'digest_i': unrecoverable packed dimensions` and
reaches the next validated source-shaped boundary,
`Schedule:preemptive`, under IEEE 1800-2023 §4.7.

The extractor regression covers the typedef-backed packed array spelling.
The existing parameter-sized unpacked-port receipt reports 10 ordinary rows
at N=2 and N=3, with Icarus Verilog 13.0 and Xcelium 24.03-s004 MATCHing all
rows, including x/z elements.
