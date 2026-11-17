#!/usr/bin/env bash
set -euo pipefail

# rustc_public is an in-tree compiler crate. Build this driver with the
# selected rustup toolchain rather than through crates.io, and fail if the
# caller did not provide the lane-local toolchain roots.
: "${RUSTUP_HOME:?set RUSTUP_HOME to the lane-local rustup root}"
: "${CARGO_HOME:?set CARGO_HOME to the lane-local cargo root}"

channel="${RUST_MIR_TOOLCHAIN:-nightly-2026-11-16}"
sysroot="$(rustup run "$channel" rustc --print sysroot)"
target="$(rustup run "$channel" rustc -vV | sed -n 's/^host: //p')"
lib="$sysroot/lib/rustlib/$target/lib"
out="${1:-rust-mir-extract}"
script_dir="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"

export RUSTC_BOOTSTRAP=1
rustup run "$channel" rustc "$script_dir/src/main.rs" \
  --edition=2024 \
  --crate-name rust_mir_extract \
  -o "$out" \
  -L dependency="$lib" \
  -L native="$sysroot/lib" \
  -C prefer-dynamic \
  -Z force-unstable-if-unmarked

echo "built $out with $(rustup run "$channel" rustc --version)"
