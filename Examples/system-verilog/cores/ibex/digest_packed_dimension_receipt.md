# Ibex SHA-2 digest packed-dimension boundary

The pinned SHA-2 source declares `digest_i` as an unpacked array of a
package typedef, `sha_word64_t [7:0]`. Slang retains this source-shaped port,
but the ordinary loader reports `decl 'digest_i': unrecoverable packed
dimensions` when the canonical E declaration boundary is reached. A
clean-room reduction with a package typedef and a parameter-sized unpacked
port reproduces the same refusal through `load_design_sv2`.

The SHA-2 package constants are already retained before this wall. No source
rewrite or packed-dimension approximation is used. Simulator rows for this
boundary remain pending because the source-wide SHA-2 module has additional
unsupported dependencies.
