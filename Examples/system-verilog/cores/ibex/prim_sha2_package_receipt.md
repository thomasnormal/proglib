# Ibex SHA-2 package-constant boundary

A fresh approved Slang extraction of the pinned `prim_sha2_pkg.sv` and its
SHA-2 module users retains `NumRound256` and the 64-element
`CubicRootPrime256` package parameter as source-shaped package metadata. The
ordinary loader no longer reports the earlier unresolved identifier at this
wall. Its bounded probe reaches the next source-shaped declaration boundary,
`digest_i: unrecoverable packed dimensions`.

The clean-room package-constant receipt was rerun with
`TMPDIR=/scratch/thomas-ahle/gate/ls-sv3/tmp-bits-package-param python3 harness/sv/batch_receipt.py --cleanroom-dir /var/tmp/thomas-ahle/fleet2/cleanroom --ordinary-timeout 120 --lean-group-size 1 --only bits_package_param_e`.
It produced eight ordinary cycles. Icarus Verilog 13.0 and Xcelium
24.03-s004 MATCHed all rows, including x/z input rows.
