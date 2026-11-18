# Rust lane toolchain

Stage 0 uses one pinned nightly for the compiler, `rustc-dev`, `rust-src`, and
Miri:

```text
nightly-2026-11-16-x86_64-unknown-linux-gnu
rustc 1.102.0-nightly (5f4effd57 2026-11-13)
cargo 1.102.0-nightly (ede6cefea 2026-11-11)
LLVM 23.1.5
miri 0.1.0 (5f4effd579 2026-11-13)
```

The installed components are `rustc-dev`, `rust-src`, and `miri`.  The lane
sets `RUSTUP_HOME`, `CARGO_HOME`, and `TMPDIR` below its scratch root; no
toolchain or build cache is taken from the user's home directory or `/tmp`.
Miri's generated sysroot is supplied explicitly through `MIRI_SYSROOT` under
that same root.

Install the pin with:

```console
rustup toolchain install nightly-2026-11-16 \
  --profile minimal \
  --component rustc-dev \
  --component rust-src \
  --component miri
```

The smoke program was run with `cargo miri run` using this pin and printed:

```text
hello from miri
```

The setup and run were executed in a user systemd scope with `MemoryMax=8G`
and `nice -n 19`.
