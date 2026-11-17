# Rust MIR Stage 0 readiness

This document closes Stage 0 item 0.5 for the Rust lane. It is a decision input
for Slice 1; it does not claim that a Lean MIR semantics exists yet. The raw
measurement and every row are in
[`rust-stage0-measurement.md`](rust-stage0-measurement.md), with the machine
report in [`rust-stage0-measurement.json`](rust-stage0-measurement.json).

The lane is pinned to `nightly-2026-11-16-x86_64-unknown-linux-gnu`: rustc
1.102.0-nightly (`5f4effd57`, 2026-11-13), cargo 1.102.0-nightly
(`ede6cefea`, 2026-11-11), and Miri 0.1.0 (`5f4effd579`, 2026-11-13). The
extractor uses the structured `rustc_public` tree and the Runtime(Optimized)
MIR flags used by Miri. The MiniRust clause source is pinned to commit
`063d784`; rustc's MIR lowering is an explicit trusted input for this lane,
as recorded in the goal decisions.

## What the measurement says

The corpus has 31 rows: ten study shapes, twenty non-printing `rustc`
`tests/ui` run-pass programs at revision
`5f4effd579500175af844241eb179e756190f1e7`, and one `println_once` control.
The command that reproduces the report is, from the repository root after
selecting the lane-local Rust roots and Miri sysroot:

```console
python3 harness/rust/measure.py --output docs/rust-stage0-measurement.json
python3 harness/rust/summarize_measurement.py docs/rust-stage0-measurement.json
```

Every row completed with status 0 under both Stacked Borrows and Tree Borrows,
and both traces had the same body, block, and statement counts. The control's
stdout was exactly `one println\n`. The report SHA-256 is
`dc22864e55517a977eba43aa7a006693adcf39e1f5113f989ca57562e0cfefbe`.

Reachable counts are unique static nodes rooted at the extracted entry body;
executed bodies and blocks are unique runtime nodes, while executed statements
are visits. The aggregate totals are bodies / blocks / statements:

| partition | reachable | executed |
|---|---:|---:|
| user | 53 / 245 / 1,686 | 52 / 172 / 1,502 |
| standard library | 1,431 / 5,524 / 24,979 | 514 / 1,585 / 18,305 |
| other compiler/runtime support | 153 / 680 / 2,357 | 60 / 225 / 2,112 |

The `println_once` control alone reaches 671 / 3,181 / 13,507 and executes
217 / 735 / 4,562. It executes 4,030 standard-library statements and reaches
`libc::unix::write`. This makes the boundary and the library, rather than a
small user's entry body, the dominant cost. Fourteen distinct intrinsic
instances and six foreign items were reached. The formatting argument in
`study_derive` and the `std::io::stdio::print_to` call behind `println_once`
remain structured unresolved call refusals because their operands are
indirect or foreign; no callee is guessed from source text.

The scaling rows show two different risks. A guarded or-pattern grows from 14
to 1,030 blocks as its parameter goes from 1 to 8. Conditionally dropped
locals grow from 9 to 131 blocks for 1 to 16 locals. Closure and iterator-chain
rows are linear over the measured range. The compiler-generated CFG therefore
needs a family-level implementation and refusal policy; it cannot be treated
as a source-level pattern tree.

## MIR node-kind census

The following counts sum the node kinds in all 31 extracted bodies. The
reachable column counts static occurrences in the envelope. The executed
column counts runtime visits in the trace; a missing executed kind was present
in reachable cleanup/control-flow but was not taken by these successful runs.
Statement and terminator names are kept separate because the semantics has a
case for each MIR node kind.

| MIR node kind | reachable | executed |
|---|---:|---:|
| `Assign` | 9,888 | 7,720 |
| `StorageLive` | 9,431 | 6,957 |
| `StorageDead` | 9,392 | 6,957 |
| `PlaceMention` | 299 | 242 |
| `SetDiscriminant` | 4 | 2 |
| `Intrinsic` | 8 | 41 |
| `terminator::Call` | 2,627 | 1,984 |
| `terminator::Return` | 1,525 | 2,228 |
| `terminator::SwitchInt` | 775 | 712 |
| `terminator::Goto` | 972 | 568 |
| `terminator::Assert` | 88 | 98 |
| `terminator::Drop` | 141 | 36 |
| `terminator::Resume` | 151 | 0 |
| `terminator::Unreachable` | 170 | 0 |

The static census contains 35,471 statement/terminator nodes and the runtime
census contains 27,545 visits. The first slice should implement these observed
families, plus the other Runtime(Optimized) cases required by its declared
scope, rather than silently treating an unobserved case as impossible. The
measurement does not show `TailCall`, `InlineAsm`, or the lowered-away
`Yield`/`CoroutineDrop` terminators; the planned policy for them is explicit
support or a named refusal.

## Churn and semantic risk

MIR is an internal compiler interface, not a stable language AST. In the
feasibility study's pinned rustc history, `syntax.rs` changed in 33 commits
since 2025-11-01 (31 non-merge), `compiler/rustc_middle/src/mir` changed in
243 commits over the year, and `rustc_mir_transform` changed in 625. Recent
semantic changes include implicit retags on typed copies, a documented change
to Call evaluation order, the replacement of `Deinit` and `NullaryOp` by
runtime checks, and new `BoxDerefTransmute` and `NullReferenceConstructed`
cases. `rustc_public` is a 0.1.0-preview interface and is not published on
crates.io; the extractor has already encountered a layout-query assertion for
escaping dynamic trait-object binders and records that as a named layout
refusal.

The standard library is the larger practical risk. The corpus reaches 1,431
standard-library bodies and 24,979 reachable standard-library statements, and
`println_once` executes 4,030 of those statements before the foreign write.
Slice 1 must therefore execute the pinned standard-library MIR and keep only a
small, explicit foreign registry. A hand-written or no-op model of `Vec`,
formatting, or allocation would change the semantics and is outside the gate.

The aliasing model is deliberately not part of Slice 1. An admissible oracle
row must have a defined result under both Stacked Borrows and Tree Borrows;
Slice 1's memory interface is otherwise strict-provenance, abstract bytes with
allocation provenance, alignment and validity checks, and an explicitly
quantified concrete-address choice. Tree Borrows can later be another memory
instance. Rows where the two oracle models disagree prove nothing for the
first slice.

## Proposed Slice 1

Slice 1 interprets the exact Runtime(Optimized) bodies in the envelope, one
node at a time. Rustc's match compilation, drop elaboration, closure lowering,
and async state transform remain named trusted lowering steps; ingestion does
not lower the envelope further. The state consists of frames, a heap and a
world/event trace. Calls use the resolved monomorphic instances in the
envelope, including standard-library bodies. The memory interface follows
MiniRust's typed encode/decode and provenance rules, with every open address
choice quantified. A single thread is in scope, with `panic=unwind` and
cleanup edges executing drop glue.

The initial supported families are:

- `Assign`, `SetDiscriminant`, `StorageLive`, `StorageDead`, and
  `PlaceMention`, with `Intrinsic` cases for the reached non-SIMD operations;
- `Goto`, `SwitchInt`, `Return`, `Unreachable`, `Drop`, `Call`, and `Assert`,
  plus `Resume`/unwind termination needed by panic paths;
- integer, boolean, character, tuple, array, slice, `str`, struct, enum,
  reference, raw-pointer, `Box`, closure, function-item and never values,
  using rustc's layout table;
- the runtime `Use`, `Ref`, `RawPtr`, `Repeat`, `Cast`, binary/unary,
  discriminant and aggregate rvalues needed by those values, including checked
  arithmetic and strict-provenance refusals;
- allocator, `exit`, `abort`, and panic-entry shims at the foreign boundary.

`println!`, formatting, floats, statics/thread-locals, unions, `TailCall`,
exposed provenance, threads and atomics, async-specific irreducible CFGs,
SIMD and inline assembly are later slices or permanent named refusals. No
unsupported construct is approximated, and no indirect call is resolved from a
source string.

The observables for the first proof layer are the exit status, panic status
(the normal Rust panic exit is 101), and a classified UB verdict. The runner
also retains the event trace so that later slices can add stdout without
changing the execution interface. The first three proof targets are a while
loop over integer MIR (gcd), a sum over a `Vec` through the standard
`slice::Iter`, and a match over an enum. Their statements must be about the
extracted MIR and its spans/`var_debug_info`; source-level names are a display
layer, not a second parser.

### Exit criteria

Slice 1 is ready for the owner's go/no-go decision only when all of these hold:

1. There are zero unexplained divergences on the in-tier corpus: the 31 Stage 0
   rows that fit the scope, non-printing `rustc` run-pass tests of at most 50
   lines, the selected Miri `tests/pass` and `tests/fail` rows, MiniRust pass
   and panic tests, and 1,000 Rustlantis programs. A row outside the tier has
   a named refusal in the envelope or interpreter; a timeout, incomplete proof,
   or failed run does not count as evidence.
2. For every in-tier Miri failure, the Lean result agrees on the UB class for
   validity, out-of-bounds, use-after-free, uninitialized, alignment,
   dangling and unchecked-overflow cases. Successful rows agree on exit and
   panic status under both borrow models.
3. The three proof targets (gcd, the `Vec` iterator sum, and enum match) are
   proved over the CFG with a first loop tactic. Loop headers are named from
   spans and `var_debug_info`; no theorem is proved by rewriting the program
   into a different construct.
4. The root `lake build`, `python3 tools/docs_check.py`,
   `python3 tools/check_private_names.py`, the extractor self-check, and the
   differential harness all pass from a clean checkout. The report and all
   refusals remain reproducible with the pinned toolchain.

The owner should stop or change levels after Slice 1 if any gate is hit: the
three proofs cost more than roughly three times the comparable Python proofs,
more than 10% of corpus loops cannot be anchored by spans; the median in-tier
program reaches over about 2,000 standard-library MIR statements or needs over
about 60 intrinsics; a deliberate re-pin costs more than two lane-weeks or
changes behavior without a reviewable diff; or the owner decides the theorem
must describe Rust source terms rather than rustc's lowered MIR. Those outcomes
are a decision, not a reason to weaken the semantics.

Slice 1 starts only after the lead records `SLICE 1: GO`. Until then, this
measurement and readiness document are the complete Stage 0 deliverable.
