# Ibex SHA-2 digest packed-dimension boundary

The pinned SHA-2 source declares `digest_i` as an unpacked array of the
package typedef `sha_word64_t [7:0]`. Slang retains this source-shaped port,
but ordinary `load_design_sv2` reports `decl 'digest_i': unrecoverable packed
dimensions` when the canonical E declaration boundary is reached. A
clean-room reduction with a package typedef and a parameter-sized unpacked
port reproduces the same refusal through `load_design_sv2`.

The extractor's existing fixed-array port path handles direct integral array
ports. This typedef-backed port currently falls through that path, so no
semantic approximation or typedef erasure was added. Simulator rows for this
boundary remain pending because the source-wide SHA-2 module has additional
unsupported dependencies.
