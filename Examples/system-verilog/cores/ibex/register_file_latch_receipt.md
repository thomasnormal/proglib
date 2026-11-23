# Ibex latch register-file ordinary-route boundary

The pinned `ibex_register_file_latch.sv` source was extracted with Slang and
its package, assertion, and generic clock-gating dependencies. The envelope
loads through `load_design_sv2`. At the default `BaseIsaRV32I` point, canonical
E binds the source-shaped generate-local constants `ADDR_WIDTH` and
`NUM_WORDS = 2**ADDR_WIDTH` under IEEE 1800-2023 §§6.20.2 and 27.4, preserves
`$bits(csr_num_e)` as a parser-native type query under §20.7, and expands the
plain register-bank generate loop. The bounded source now passes the former
`AlwaysLatch` process-kind wall and reaches the next validated constant
refusal, `InvalidExpression` in `LockstepOffsetW`. The result is a valid
ordinary-route boundary, not a source rewrite. At the CHERIoT point the
bounded source still reaches the retained
`UninstantiatedDefSymbol:expression: en_i` module boundary.

Xcelium 24.03-s004 runs the unchanged source for initial x, write/read,
zero-register, and x/z-address rows. Icarus Verilog 13.0 rejects the unchanged
module header's package-import form, so no Icarus oracle result is claimed.
The Xcelium output is the same four-row trace used for the bounded flip-flop
register-file receipt.
