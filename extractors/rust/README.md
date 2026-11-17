# rustc_public MIR extractor

`rust-mir-extract` is a thin rustc driver over the pinned nightly's
`rustc_public` API. The compiler parses the Rust source and performs lowering;
the driver reads the resulting public MIR tree after analysis and writes one
JSON envelope. It never consumes `-Zdump-mir`, `--emit mir`, or any other text
dump.

The envelope is versioned as `lean-surfaces.rust.mir.v0` and contains:

- the compiler and Miri versions and Miri's exact MIR flags;
- the entry instance and the monomorphic instances reachable from it;
- each available `Body`, including blocks, statements, terminators,
  `var_debug_info`, and source spans;
- call edges, with direct callees resolved through `Instance::resolve` and
  indirect/foreign edges explicitly marked unresolved;
- side tables for types and rustc layouts, spans, definitions, allocations,
  and global allocations.

Anything that rustc_public does not expose as a structured value remains a
named unresolved edge or a driver error. It is never reconstructed from a
string representation.

## Build and run

The build script expects the lane-local roots from `docs/rust-toolchain.md`:

```console
export RUST_LANE_ROOT=/path/to/your/rust-lane-root
export RUSTUP_HOME="$RUST_LANE_ROOT/rustup"
export CARGO_HOME="$RUST_LANE_ROOT/cargo"
export TMPDIR="$RUST_LANE_ROOT/tmp"
extractors/rust/build.sh "$RUST_LANE_ROOT/rust-mir-extract"
```

The binary is dynamically linked to the same nightly's compiler libraries, so
set its library path when invoking it:

```console
export LD_LIBRARY_PATH="$RUSTUP_HOME/toolchains/nightly-2026-11-16-x86_64-unknown-linux-gnu/lib"
"$RUST_LANE_ROOT/rust-mir-extract" \
  --crate-name=hello --edition=2024 hello.rs --crate-type=bin \
  -o hello-bin --rust-mir-output hello.mir.json
```

`--rust-mir-output PATH` is consumed by the driver and is not forwarded to
rustc. The Miri flags are added to the rustc argument list unless the exact
flag is already present. A second run on the same input produces byte-identical
JSON; metadata tables are sorted by their stable handle before writing.

The extractor must be run against a sysroot built with `-Zalways-encode-mir`
(Miri's generated sysroot is the intended one). A body that is unavailable in
that sysroot is retained as an instance with `has_body: false`; this is a
structured refusal boundary, not a text fallback.
