# Rust MIR stage 0 measurement

This is the Stage 0 item 0.4 measurement for the pinned Rust lane. It uses the
same Runtime(Optimized) MIR flags as the extractor and Miri. The machine-readable
report is [rust-stage0-measurement.json](rust-stage0-measurement.json); the input
corpus and its upstream revision are recorded in
[harness/rust/measurement_manifest.json](../harness/rust/measurement_manifest.json).

The run covered 31 programs: ten small study shapes, twenty non-printing
`rustc` `tests/ui` run-pass programs, and one control containing exactly one
`println!`. Every row completed with status 0 under both Stacked Borrows and
Tree Borrows, and the two traces had equal body/block/statement counts. The
Miri output for the control was exactly `one println\n`.

## Reproducing the numbers

The pinned toolchain and generated Miri sysroot must be selected through the
lane-local roots. From the repository root, set `RUST_LANE_ROOT` to the lane's
scratch root and run:

```console
export RUSTUP_HOME="$RUST_LANE_ROOT/rustup"
export CARGO_HOME="$RUST_LANE_ROOT/cargo"
export TMPDIR="$RUST_LANE_ROOT/tmp"
export MIRI_SYSROOT="$RUST_LANE_ROOT/miri-cache/nightly-2026-11-16-x86_64-unknown-linux-gnu"
export RUST_MIR_EXTRACTOR="$RUST_LANE_ROOT/rust-mir-extract"
python3 harness/rust/measure.py --output docs/rust-stage0-measurement.json
python3 harness/rust/summarize_measurement.py docs/rust-stage0-measurement.json
```

`measure.py` invokes the structured `rustc_public` extractor for each source,
then runs each source twice with
`rustc_const_eval::interpret=info`. The trace parser enters at the extracted
entry body, so Rust's `std::rt` launcher and shutdown are outside the count.
A block marker identifies a MIR block; subsequent structured step records are
matched to that block's extracted statements and terminator. Miri's
`ConstEvalCounter` records have no MIR node and are ignored. Reachable body,
block and statement counts are unique static nodes in the envelope. Executed
body and block counts are unique runtime nodes; executed statement counts are
runtime statement visits (loop iterations therefore count repeatedly).
`statement_sites`, `block_visits`, and the per-body block sets are retained in
the JSON for audits. No textual MIR dump or source re-parser is used.

The extractor records a named layout refusal for dynamic trait-object types
because the pinned `rustc_public` layout query can assert on escaping binders.
That refusal is data in the envelope and does not affect these counts.

## Corpus counts

The full per-program table below is emitted by
`python3 harness/rust/summarize_measurement.py docs/rust-stage0-measurement.json`.
`R` is reachable (static) bodies/blocks/statements, `E` is executed
unique bodies/blocks and statement visits, and `U`/`S` are the executed user
and standard-library partitions respectively. The separate `other` partition
contains compiler/runtime support instances whose names are neither the local
crate nor `core`, `alloc`, `std`, `compiler_builtins`, `panic_unwind`, or
`unwind`.

| program | category | R: bodies / blocks / statements | E: bodies / blocks / statements | U: bodies / blocks / statements | S: bodies / blocks / statements |
|---|---|---:|---:|---:|---:|
| `study_for_vec` | study | 127 / 391 / 1,619 | 75 / 208 / 1,416 | 1 / 11 / 151 | 66 / 160 / 886 |
| `study_iterator_chain` | study | 58 / 190 / 859 | 15 / 41 / 2,053 | 4 / 11 / 198 | 7 / 16 / 1,258 |
| `study_match_or_guard` | study | 21 / 72 / 497 | 2 / 15 / 115 | 2 / 15 / 115 | 0 / 0 / 0 |
| `study_closures` | study | 22 / 59 / 435 | 3 / 9 / 97 | 3 / 9 / 97 | 0 / 0 / 0 |
| `study_drop_struct` | study | 31 / 90 / 499 | 6 / 17 / 150 | 1 / 5 / 50 | 5 / 12 / 100 |
| `study_generic_trait` | study | 22 / 58 / 387 | 2 / 5 / 35 | 2 / 5 / 35 | 0 / 0 / 0 |
| `study_question_mark` | study | 25 / 85 / 516 | 6 / 28 / 171 | 2 / 14 / 103 | 1 / 1 / 7 |
| `study_async` | study | 44 / 131 / 689 | 13 / 30 / 187 | 4 / 16 / 89 | 9 / 14 / 98 |
| `study_derive` | study | 272 / 1,224 / 4,937 | 156 / 563 / 11,445 | 1 / 10 / 71 | 143 / 520 / 10,864 |
| `study_while_gcd` | study | 21 / 58 / 412 | 2 / 8 / 119 | 2 / 8 / 119 | 0 / 0 / 0 |
| `rustc_ivec-pass-by-value` | rustc run-pass | 75 / 236 / 774 | 54 / 142 / 621 | 2 / 6 / 13 | 48 / 129 / 582 |
| `rustc_vec-repeat-with-cast` | rustc run-pass | 1 / 1 / 4 | 1 / 1 / 4 | 1 / 1 / 4 | 0 / 0 / 0 |
| `rustc_nested-closure-call` | rustc run-pass | 22 / 56 / 396 | 3 / 6 / 49 | 3 / 6 / 49 | 0 / 0 / 0 |
| `rustc_closure-returning-closure` | rustc run-pass | 22 / 57 / 408 | 3 / 7 / 61 | 3 / 7 / 61 | 0 / 0 / 0 |
| `rustc_move-arg` | rustc run-pass | 21 / 54 / 386 | 2 / 4 / 39 | 2 / 4 / 39 | 0 / 0 / 0 |
| `rustc_i32-sub` | rustc run-pass | 20 / 53 / 385 | 1 / 3 / 38 | 1 / 3 / 38 | 0 / 0 / 0 |
| `rustc_return-nil` | rustc run-pass | 2 / 3 / 7 | 2 / 3 / 7 | 2 / 3 / 7 | 0 / 0 / 0 |
| `rustc_match-bot-2` | rustc run-pass | 2 / 3 / 6 | 2 / 3 / 6 | 2 / 3 / 6 | 0 / 0 / 0 |
| `rustc_let-destruct-ref` | rustc run-pass | 20 / 52 / 383 | 1 / 2 / 36 | 1 / 2 / 36 | 0 / 0 / 0 |
| `rustc_multi-let` | rustc run-pass | 20 / 52 / 383 | 1 / 2 / 36 | 1 / 2 / 36 | 0 / 0 / 0 |
| `rustc_binop-mutate-lhs-in-rhs` | rustc run-pass | 20 / 53 / 394 | 1 / 3 / 47 | 1 / 3 / 47 | 0 / 0 / 0 |
| `rustc_const-prop-ice3` | rustc run-pass | 1 / 1 / 20 | 1 / 1 / 20 | 1 / 1 / 20 | 0 / 0 / 0 |
| `rustc_if-ret` | rustc run-pass | 2 / 3 / 6 | 2 / 3 / 6 | 2 / 3 / 6 | 0 / 0 / 0 |
| `rustc_return-in-block-tuple` | rustc run-pass | 1 / 1 / 5 | 1 / 1 / 5 | 1 / 1 / 5 | 0 / 0 / 0 |
| `rustc_vector-no-ann-2` | rustc run-pass | 62 / 196 / 599 | 42 / 113 / 445 | 1 / 4 / 5 | 39 / 104 / 425 |
| `rustc_generic-newtype-struct` | rustc run-pass | 1 / 1 / 4 | 1 / 1 / 4 | 1 / 1 / 4 | 0 / 0 / 0 |
| `rustc_match-on-negative-integer-ranges` | rustc run-pass | 20 / 62 / 444 | 1 / 9 / 77 | 1 / 9 / 77 | 0 / 0 / 0 |
| `rustc_by-value-self-method-on-int` | rustc run-pass | 2 / 3 / 4 | 1 / 2 / 3 | 1 / 2 / 3 | 0 / 0 / 0 |
| `rustc_new-unsafe-pointers` | rustc run-pass | 1 / 1 / 7 | 1 / 1 / 7 | 1 / 1 / 7 | 0 / 0 / 0 |
| `rustc_empty-mutable-vec` | rustc run-pass | 8 / 22 / 50 | 8 / 16 / 58 | 1 / 3 / 3 | 7 / 13 / 55 |
| `println_once` | println control | 671 / 3,181 / 13,507 | 217 / 735 / 4,562 | 1 / 3 / 8 | 189 / 616 / 4,030 |

Across all rows, reachable totals are user 53/245/1,686, standard 1,431/5,524/24,979,
and other 153/680/2,357 (bodies/blocks/statements). Executed totals are user
52/172/1,502, standard 514/1,585/18,305, and other 60/225/2,112. The ten
study shapes have median reachable 28/87.5/507.5 and median executed
6/22.5/160.5; the twenty run-pass rows have median reachable 14/37/216.5 and
median executed 1/3/36. The println control reaches 671/3,181/13,507 and
executes 217/735/4,562.

## Runtime node and boundary census

The executed node counts over all 31 rows are: `Assign` 7,720,
`StorageLive` 6,957, `StorageDead` 6,957, `PlaceMention` 242,
`SetDiscriminant` 2, `Intrinsic` 41, and terminators `Return` 2,228,
`Call` 1,984, `SwitchInt` 712, `Goto` 568, `Assert` 98, and `Drop` 36.
These counts are emitted by the same summarizer command above.

Fourteen distinct reached intrinsic instances were observed:

```text
std::intrinsics::atomic_cxchg::<u32, std::intrinsics::AtomicOrdering::Acquire, std::intrinsics::AtomicOrdering::Relaxed>
std::intrinsics::atomic_load::<u32, std::intrinsics::AtomicOrdering::Acquire, false>
std::intrinsics::atomic_load::<u64, std::intrinsics::AtomicOrdering::Relaxed, false>
std::intrinsics::atomic_load::<u8, std::intrinsics::AtomicOrdering::Relaxed, false>
std::intrinsics::atomic_load::<usize, std::intrinsics::AtomicOrdering::Relaxed, false>
std::intrinsics::atomic_store::<u64, std::intrinsics::AtomicOrdering::Relaxed, false>
std::intrinsics::atomic_xchg::<u32, std::intrinsics::AtomicOrdering::Release>
std::intrinsics::black_box::<std::string::String>
std::intrinsics::ctpop::<usize>
std::intrinsics::exact_div::<usize>
std::intrinsics::integer_max::<usize>
std::intrinsics::integer_min::<usize>
std::intrinsics::is_val_statically_known::<bool>
std::intrinsics::ptr_offset_from_unsigned::<u8>
```

Six distinct foreign items were reached:

```text
alloc::alloc::__rust_alloc
alloc::alloc::__rust_dealloc
alloc::alloc::__rust_no_alloc_shim_is_unstable_v2
alloc::alloc::__rust_realloc
libc::unix::write
std::intrinsics::miri_promise_symbolic_alignment::miri_promise_symbolic_alignment
```

Two executed call sites remain deliberately unresolved because their MIR
operands are indirect or foreign: the formatting argument in `study_derive`
and the `std::io::stdio::print_to` call behind `println_once`. The report keeps
both names and blocks as structured refusals; it does not infer a callee from
source text.

## Construct-size rows

These rows are static extractor measurements of generated functions, emitted in
the JSON's `construct_sizes` array. Their command is the same corpus command
above; `--no-constructs` omits them. The columns are local user bodies/blocks/
statements.

| construct | parameter | bodies | blocks | statements |
|---|---:|---:|---:|---:|
| or-pattern guard | 1 | 2 | 14 | 63 |
| or-pattern guard | 2 | 2 | 22 | 71 |
| or-pattern guard | 3 | 2 | 38 | 87 |
| or-pattern guard | 4 | 2 | 70 | 119 |
| or-pattern guard | 5 | 2 | 134 | 183 |
| or-pattern guard | 6 | 2 | 262 | 311 |
| or-pattern guard | 7 | 2 | 518 | 567 |
| or-pattern guard | 8 | 2 | 1,030 | 1,079 |
| conditionally dropped locals | 1 | 1 | 9 | 19 |
| conditionally dropped locals | 2 | 1 | 19 | 38 |
| conditionally dropped locals | 4 | 1 | 35 | 76 |
| conditionally dropped locals | 8 | 1 | 67 | 152 |
| conditionally dropped locals | 16 | 1 | 131 | 304 |
| closures | 1 | 2 | 5 | 29 |
| closures | 2 | 3 | 8 | 49 |
| closures | 4 | 5 | 14 | 89 |
| closures | 8 | 9 | 26 | 169 |
| closures | 16 | 17 | 50 | 329 |
| iterator chain | 1 | 3 | 9 | 73 |
| iterator chain | 2 | 4 | 12 | 83 |
| iterator chain | 4 | 6 | 18 | 103 |
| iterator chain | 8 | 10 | 30 | 143 |
| iterator chain | 16 | 18 | 54 | 223 |

The guarded or-pattern grows from 14 to 1,030 blocks as eight positions are
added; conditional drops grow from 9 to 131 blocks over 16 locals. Closures
and iterator chains grow linearly in these rows. The generated rows measure
MIR emitted by the pinned compiler, not a hand-written lowering.

## Decision input

The gate sees a sharp difference between local code and the library. Most
small run-pass rows execute one to three local bodies and only a few dozen
local statements, while a Vec, derive, or `println!` row reaches dozens to
hundreds of standard-library bodies. `println!` executes 4,030 standard
statements and reaches `libc::unix::write`; `study_derive` executes 10,864
standard-library statement visits. The standard library and foreign boundary,
not the local MIR node count, are therefore the dominant Stage 1 cost. The
or-pattern guard is the only measured construct with exponential CFG growth.
