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

## Stage 0 MIR measurement

`measure.py` runs the structured extractor and the Miri interpreter trace over
the 31-row corpus in `measurement_manifest.json`. It records unique reachable
bodies, blocks, and statements from the envelope, plus unique executed
bodies/blocks and executed statement visits from
`RUSTC_LOG=rustc_const_eval::interpret=info`. The trace starts at the
extracted entry body, so the Rust launcher is not counted. Both Stacked Borrows
and Tree Borrows are run for every row.

```console
export RUST_LANE_ROOT=/path/to/your/rust-lane-root
export RUSTUP_HOME="$RUST_LANE_ROOT/rustup"
export CARGO_HOME="$RUST_LANE_ROOT/cargo"
export TMPDIR="$RUST_LANE_ROOT/tmp"
export MIRI_SYSROOT="$RUST_LANE_ROOT/miri-cache/nightly-2026-11-16-x86_64-unknown-linux-gnu"
export RUST_MIR_EXTRACTOR="$RUST_LANE_ROOT/rust-mir-extract"
python3 harness/rust/measure.py --output docs/rust-stage0-measurement.json
python3 harness/rust/summarize_measurement.py docs/rust-stage0-measurement.json
```

The report schema is `lean-surfaces.rust.mir-measurement.v0`. The summary
script is intentionally a separate deterministic projection of the JSON, so
every scalar in `docs/rust-stage0-measurement.md` has a command that regenerates
it.
