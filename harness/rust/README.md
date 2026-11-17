# Rust Miri oracle harness

`miri_oracle.py` runs a standalone Rust source file or a Cargo package under
the pinned nightly's Miri twice. The first run uses Miri's default Stacked
Borrows model; the second adds `-Zmiri-tree-borrows`. Both runs use the same
lane-local generated sysroot and these deterministic flags:

```text
-Zmiri-deterministic-concurrency
-Zmiri-deterministic-floats
-Zmiri-seed=0
-Zmiri-num-cpus=1
-Zmiri-isolation-error=abort
```

Set the roots from `docs/rust-toolchain.md` before invoking it. `MIRI_SYSROOT`
must name the generated sysroot (the default is
`$RUST_LANE_ROOT/miri-cache/<pinned-toolchain>`). For a standalone source:

```console
python3 harness/rust/miri_oracle.py harness/rust/fixtures/ok.rs \
  --output oracle.json
```

The JSON schema is `lean-surfaces.rust.miri-oracle.v0`. Every model row records
the exact command and flags, pinned compiler/Miri versions, exit status, raw
stdout/stderr, and two explicit booleans (`panic`, `ub`). The conservative
verdicts are `ok`, `exit`, `panic`, `ub`, `timeout`, or `tool_error`; an unrecognized
nonzero result is a refusal rather than a guessed runtime classification.

The checked-in smoke battery exercises all four observable categories:

```console
python3 harness/rust/miri_oracle.py --self-test
```

The fixture `exit.rs` intentionally returns status 7. Its empty diagnostic
stream and nonzero status are recorded as the `exit` verdict.
