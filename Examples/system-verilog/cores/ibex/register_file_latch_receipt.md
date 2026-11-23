# Ibex latch register-file ordinary-route boundary

The pinned `ibex_register_file_latch.sv` source was extracted with Slang and
its package, assertion, and generic clock-gating dependencies. The envelope
loads through `load_design_sv2`. At the default `BaseIsaRV32I` point, the
ordinary E probe reaches the source-shaped generate-local constant boundary
with `GenerateDecl:LocalParam: generate-local parameter 'NUM_WORDS': unbound
parameter 'NUM_WORDS'`. At the CHERIoT point it reaches the retained
`UninstantiatedDefSymbol:expression: en_i` module dependency. These are
named ordinary-route refusals, not source rewrites.

Xcelium 24.03-s004 runs the unchanged source for initial x, write/read,
zero-register, and x/z-address rows. Icarus Verilog 13.0 rejects the unchanged
module header's package-import form, so no Icarus oracle result is claimed.
The Xcelium output is the same four-row trace used for the bounded flip-flop
register-file receipt.
