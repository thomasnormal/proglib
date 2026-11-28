# Pinned C/C++ frontend CI proposal

`tools/leanc --self-test` requires the exact Clang 21.1.8 frontend line and
the four parser plugins used by `extractors/c`. Hosted CI currently installs an
unversioned apt `clang` and builds none of those plugins, so the self-test
cannot qualify the C extractor there.

The CI-owned setup should install the conda-forge Clang/LLVM 21.1.8 packages
with their build strings pinned to the verified artifacts used by this lane.
The setup should cache that environment by the package-lock hash and build the
four plugins from the checked-out sources using the command in
`extractors/c/README.md`. It should export `LEAN_C_CLANG`,
`LEAN_C_STRING_BYTES_PLUGIN`, `LEAN_C_FLOATING_BITS_PLUGIN`,
`LEAN_C_RECORD_LAYOUT_PLUGIN`, and `LEAN_C_STRUCTURED_TYPE_PLUGIN` before
running `tools/leanc --self-test` and the C determinism gates.

The frontend executable must remain the pinned host-compatible Clang binary.
The plugin environment supplies matching headers and libraries for linking,
while the exported frontend path continues to use the verified profile. A
cache hit must still run `clang --version`, plugin self-tests, and the source
hash checks. A cache miss rebuilds the plugins and refreshes the cache.

No repository fallback to apt Clang, an unpinned conda build, or missing-plugin
degradation is proposed. The C extractor's approved-parser requirement stays a
loud failure when the pinned artifacts are unavailable.

**CPP-CI READY** — implementation belongs to the CI-owning lane, with this
proposal providing the exact package, environment, plugin, cache, and gate
requirements for review.
