# Rust Slice 1

This slice implements the MIR node census groups in the approved
`rustc_public` envelope.  It covers `Assign`, `StorageLive`, `StorageDead`, `PlaceMention`, structured `Deref` and
`Field` projections, `Ref` and tuple aggregates, pointer cells with provenance
and chosen addresses, `Use` rvalues, typed integer and pointer-preserving `Cast`
rvalues, constant operands, control flow, resolved calls, normal drop edges, and
explicit refusal boundaries for cleanup, intrinsics, and foreign operations. The
implementation is 1335 lines in `LeanModels/Rust/Semantics.lean`, with 134 lines
of AST declarations, 490 lines of JSON decoding, and 38 lines of the literal-envelope loader.

The local fixture count is separate from the Stage 0 corpus.  The last measured
counter is `SLICE1-ROWS 20/30, diverging 0`, at the lane's parked tip (the
commit "rust: expose typed equality refusal operands").  It was not re-measured
after the land1 review fixes recorded at the end of this file: the corpus
envelopes are not checked in, and the audit re-extracts them with the pinned
nightly extractor.

The 30 non-printing Stage 0 rows were audited with the structured extractor:

```console
python3 harness/rust/slice1_audit.py --output docs/rust-slice1-audit.json
```

The report contains 30 rows, 23 decided rows, 7 named refusals, and zero
divergences. The audit extracts every envelope, loads each one into Lean, runs
`runOutcome` for all of them in one `lake env lean` process (`#eval`), and
compares each return, panic or UB outcome with the Stage 0 Miri verdict; a
refusal or fuel exhaustion is a named refusal.  Every row of this corpus exits
0 under Miri, so a wrong value that still returns cannot show up as a
divergence: panic and UB rows are needed before `diverging 0` carries weight.
Refusal reasons name the MIR node at which the run stopped, or the call target that
has no MIR body.  The `println_once` control is excluded by
default and can be included with `--include-control`.  Each row records the
extractor wall time.  The 30-row audit took 2.910 s in total, with row times
from 0.028 s to 0.557 s.

When a typed `Use` cannot read its place, the refusal records the operand cell
and MIR place.  The iterator-chain row now uses each resolved closure body's
extracted `arg_count` to spread the final tuple argument into its formal locals.
This removes the earlier false `uninit` local caused by binding the tuple as one
slot.  The row remains `out_of_fuel` even when the same kernel runner is probed
with fuel 20,000 and 100,000.  It therefore remains an explicit fuel/divergence
boundary rather than an invented remainder value.

The closure-returning-closure row exercises the same ABI rule with a two-element
tuple passed to a three-argument closure body.  The tuple fields bind to the two
integer locals, the checked addition and assertion execute, and the row now
returns normally under both Miri models.

The atomic-load path decodes the extracted `Atomic<usize>` aggregate from its
allocation bytes and projects field zero through the type argument layout.  The
`study_drop_struct` row therefore passes the atomic operation and reaches its
next boundary, the missing MIR body for `caller_location`.  That foreign runtime
helper remains a named refusal with no guessed panic metadata.

The `study_async` cast boundary is `std::ptr::without_provenance`: its MIR
transmutes a `usize` value into a raw pointer and then applies `PtrToPtr`. The
current pointer representation requires provenance, so the operand is retained
as an integer and the second cast reports a typed refusal with target layout 27.
No provenance is fabricated from the integer address.

The remaining `study_derive` refusal occurs in `core::fmt::Arguments::as_str`.
Its MIR applies `BitAnd` between a pointer cell with provenance 28 and integer
constant 1 while checking formatting metadata. The integer bitwise evaluator
therefore refuses the mixed pointer/integer operands and reports both cells.
The operation is not reduced to an address comparison.

The Repeat family is parsed from the structured const-generic value in the
MIR envelope and constructs a repeated aggregate cell. The Cast family decodes
`IntToInt` through the target integer layout and preserves provenance for
`PtrToPtr`.  A `Transmute` reinterprets an integer at an integer target's width
and signedness, keeps an integer as an address without provenance at a raw
pointer target, and keeps a pointer at a pointer target; every other transmute
refuses.  `MutToConstPointer` and `Unsize` coercions keep their operand (the
unsized metadata is not represented, and reading it refuses); the other pointer
coercions refuse.  An exposed-provenance cast of an integer to a raw pointer is
the address without provenance, and dereferencing it refuses.  The
`rustc_vec-repeat-with-cast` corpus row is decided after its Repeat value
reaches a zero-sized return.

Pointer constants retain the extractor's global-allocation identity and
resolve it through the envelope's global table before reading bytes. Local
references and allocation pointers use separate provenance classes, so a local
ID cannot alias an allocation-table index. The address-independence theorem
continues to compare pointers by provenance while allowing their chosen
addresses to differ.

Enum aggregates retain their variant index and fields. `Downcast` checks that
index before `Field` reads, and `Discriminant` exposes it as a typed integer.
That is the discriminant only for enums with default discriminants: the
envelope does not carry declared discriminant values, so for
`enum E { A = 7, B = 9 }` a `match` reaches its `unreachable` arm in the model
(a known wrong answer, listed below).
Direct enum layouts carry extracted tag offsets, tag widths, variant counts, and
payload type arguments. A direct enum can therefore be decoded from allocation
bytes even when an inactive variant payload contains uninitialized bytes. Local
`Ref` and `AddressOf` values retain frame-local provenance before a call shares
them with the callee. The `study_question_mark` corpus row now returns normally
through `Option<i32>` comparison.
Cross-frame projection shares nested local pointers with the frame that owns the
enclosing aggregate. Singleton ABI aggregate wrappers are unwrapped only when a
scalar operand is consumed. The `study_closures` row now reaches its checked
addition and returns normally.
The `Le` binary operation now uses the decoded signed or unsigned integer
values from the layout table. These cases decide the negative-integer-range
corpus row without treating its signed bytes as an unsigned order comparison.

The three rows are the checked-in sources
`Examples/rust/assign/main.rs`, `Examples/rust/storage/main.rs`, and
`Examples/rust/place_mention/main.rs`.  Their envelopes were regenerated by
the pinned `rustc_public` extractor.  The oracle command is run once per row
as follows, after selecting the lane-local roots from `harness/rust/README.md`.

```console
python3 harness/rust/miri_oracle.py Examples/rust/assign/main.rs
python3 harness/rust/miri_oracle.py Examples/rust/storage/main.rs
python3 harness/rust/miri_oracle.py Examples/rust/place_mention/main.rs
```

Each row returned `ok` with exit status 0 under both Stacked Borrows and Tree
Borrows.  Wall-clock measurements for one invocation of the two-model command
were 0.599 s, 0.582 s, and 0.571 s respectively on the lane host.  No fixture
diverged or timed out.  These local fixtures are not Stage 0 corpus rows, so
they do not change the corpus counter.

The next control-flow family adds `Goto`, `SwitchInt`, `Return`, and
`Assert` with `Continue` unwind edges.  `Unreachable` is represented as a
named refusal because it has no successful trace.  The three control-flow
rows are `Examples/rust/control/main.rs`, `Examples/rust/assert/main.rs`, and
`Examples/rust/switch/main.rs`.  Miri returned `ok` with exit status 0 under
both borrow models for all three.  Two-model invocations measured 0.645 s,
0.635 s, and 0.622 s respectively.  These local fixtures do not change the
Stage 0 corpus counter.

The CFG runner consumes one block per fuel unit.  `SwitchInt` resolves an
integer operand against ordered branch values and otherwise takes the default
target.  The supported assertion transition reaches its target exactly when
the condition equals `expected`; division-by-zero and overflow assertions are
therefore explicit refusals until their checked arithmetic and panic paths are
implemented.  `Copy` and `Move` operands now read initialized integer locals,
and the supported equality, bit-and, and division rvalues are evaluated
without lowering the MIR.

The state is a finite map of local IDs to uninitialized, integer, pointer, or
aggregate cells. A step emits one event and updates that map. Allocated
constant bytes are checked before decoding into cells. Zero-sized aggregates
remain explicit, and non-empty aggregates are not guessed as zero.

The derived `runOutcome` reports a returned trace or a named refusal outcome.
No unsupported node is lowered to a different construct.

`Step` is the definition of one statement transition.  `InSteps` composes those
transitions, and `statementsRun_in_steps` plus `bodyRun_in_steps` prove that the
kernel-reducible statement and body runners are contained in the relation.
`ProgramSteps` is the envelope-level relation.  Its call constructor records the
resolved edge, argument binding, callee `CfgSteps` trace, return value, and
caller continuation.  `cfgRunProgram_in_steps` proves that the kernel-reducible
program runner is contained in `ProgramSteps`, and `ProgramInSteps` exposes that
fuel-free relation.  The three Lean example proofs check that each loaded envelope has a
successful run.  They also expose the exact event traces through the reducible
runner when inspecting a row.

The resolved-call family has a decided row in `Examples/rust/call`.  The
envelope preserves the resolved edge in its `calls` table.  The runner enters
the resolved callee body, copies its integer return local into the caller's
destination, records a call event, and continues at the target block.  Miri
returned `ok` with status 0 under both models.  The measured two-model command
completed in 10.023 s on a cold invocation.  This local fixture does not change
the Stage 0 corpus counter.

The cleanup family retains `Drop` with a normal target and a recorded cleanup
target, plus `Resume` as a named refusal. `Examples/rust/drop/main.rs` has a
variant-zero fieldless aggregate construction before the drop. The loader
represents that zero-sized value as a unit cell and the row returns normally.
Miri returned `ok`, status 0 under both borrow models, in 1.257 s.

The final intrinsic/foreign boundary is represented by
`Examples/rust/foreign/main.rs`, which calls `std::process::exit(7)`.  Its
resolved instance has no MIR body and its call has no normal target.  The
runner refuses this foreign registry operation without guessing an exit event.
Miri returned `exit`, status 7, under both borrow models.  The two-model
invocation measured 2.828 s.  Intrinsics, foreign calls without a registry
entry, calls with a missing body, calls with cleanup unwind, and calls with no
normal continuation are named refusals in this slice.

The allocator family was traced through `Global::allocate` and
`alloc_impl_runtime` in the `study_for_vec`, `rustc_ivec-pass-by-value`, and
`rustc_vector-no-ann-2` envelopes.  Their first current boundary is the
`Layout::size` read through a shared pointer whose target frame local is still
`uninit`.  The later allocator shims have no MIR body and cannot be entered
until that frame state is resolved.  The runner reports the exact pointer and
target-frame refusal instead of manufacturing a layout value or allocation.
An allocator registry would also require a state transition that chooses fresh
provenance, address, bytes, and validity, which is outside this relation.

The required theorem rows are checked-in user functions.  `Examples/rust/loop`
proves the exact executable trace of a countdown loop.  Its Miri oracle invocation took
15.299 s and returned `ok` with status 0 under both borrow models.  The extra
time is the cold compilation of the loop's extracted program.

`Examples/rust/call` proves the resolved user call trace, including argument
binding, the callee return-local copy, the call event, and the caller's
continuation.  `Examples/rust/std_identity` proves the analogous trace for
`std::convert::identity::<i32>` directly from its extracted standard-library
MIR body.  The identity oracle invocation took 2.444 s and returned `ok` with
status 0 under both borrow models.  These are three local theorem rows, and
the checked-in `ProgramInSteps` rows also cover the assignment, storage,
place-mention, control-flow, call, loop, and drop fixtures.  They do not
change the Stage 0 corpus counter.  `run`, `cfgRunProgram` and `ProgramSteps`
still use the older call rule (the callee state starts empty and the arguments
are read from it), which `runOutcome` replaced; nothing relates the two runners.

## Slice 1 exit record

The D1 corpus audit reports 30 rows, 20 decided rows, 10 named refusals, and
zero diverging rows (measured before the land1 fixes below).  Each row's
refusal is tied to the first unsupported rvalue or terminator, an unavailable
callee, or the absence of a checked-in relation row.  The audit command and
its per-row extractor timings are recorded in `docs/rust-slice1-audit.json`.
The pinned Stage 0 Miri report records the exit, panic, and UB verdict for all
31 measured rows under both borrow models.  The Lean semantics is 1335 lines.
The checked-in theorem rows include a user loop, a resolved user call, and a
standard-library identity call proved from its extracted MIR body.

`SLICE 1 CHECKPOINT` is recorded in the lane journal after D1. The lane continues
with the memory/value family and the all-inputs gcd proof before declaring READY.

The relation integrity audit used this Lean command:

```console
cat > /tmp/rust_relation_audit.lean <<'EOF'
import LeanModels.Rust.Semantics
#print LeanModels.Rust.ProgramSteps
#print LeanModels.Rust.ProgramInSteps
#print axioms LeanModels.Rust.cfgRunProgram_in_steps
#print axioms LeanModels.Rust.run_in_steps
EOF
lake env lean /tmp/rust_relation_audit.lean
```

The printed signatures show no fuel parameter in either public relation.  The
two containment theorems report only `propext`, `Classical.choice`, and
`Quot.sound` in their axiom dependencies.

The D3 proof preparation is checked in under `Examples/rust/gcd/`.  Its loaded
envelope contains the extracted `gcd` body from the Stage 0 corpus.  The
diagnostic runner reaches that body for arbitrary initial `u32` locals, and the
spec file checks a concrete `(48,18)` run.  The proof file proves the
all-inputs Euclidean loop theorem with strong induction and the `Nat.gcd_rec`
lemma.  `gcd_all_inputs_cfg` states, for every pair of natural numbers, that
the single-body runner `cfgRunOutcome` on the extracted `gcd` body (checked
equal to the loaded envelope's body by `rfl`) returns `Nat.gcd a b`.  The run
starts from a hand-built state holding the two arguments and a one-entry `u32`
layout table (`gcdType`), not the envelope's table, and the theorem goes
through neither `main`, the program runner `runOutcome`, nor `ProgramSteps`.

The proof-cost measurement was rerun from the repository root with

```console
wc -l harness/rust/measurement_programs/study/10_while_gcd.rs Examples/rust/gcd/proof.lean
python3 - <<'PY'
import subprocess, time
started = time.monotonic()
result = subprocess.run(["lake", "build", "Examples.rust.gcd.proof"])
print(f"exit={result.returncode} elapsed_seconds={time.monotonic() - started:.3f}")
PY
```

The source has 12 lines and the proof file had 339 lines (349 after land1).
The final induction theorems occupied lines 261--318, or 58 lines, which is
4.83 proof lines per source line.  Including the explicit extracted-body
fixture and its transition lemmas, the checked-in proof is 28.25 lines per
source line.  Counted against the 8-line `gcd` function alone, the symbolic
step lemmas and the induction are 200 non-blank lines, against 11 tactic lines
for the Python lane's `gcd` proof with `py_vcgen`.  The measured
incremental build took 6.208 seconds and exited 0.  The expensive part is the
repeated symbolic execution of the extracted blocks and the bridge between
`Nat` remainder facts and the signed `Int` cells.  The induction itself is the
short portion of the proof.

## Landing review (land1)

The land1 review rebuilt every Rust target and added fixes on top of the
parked lane commits.  Ten example proofs were red: `projectCell` had become
well-founded recursion (the kernel cannot unfold it, so `decide` over `run` got
stuck) and `DecidableEq` was dropped from the nested `Cell` type; the extracted
gcd proof did not unfold the new `findTypeLayout`.  These were repaired without
changing a statement.  The following silent wrong answers were turned into
exact results or refusals:

- overflow-checked `Add`/`Sub`/`Mul` were checked against the i32 range for
  every type, and an unknown operator meant "overflow";
- `Div` and `Rem` used Lean's Euclidean `/` and `%` (Rust truncates);
- `BitAnd` and `BitXor` mapped negative operands to 0;
- `Transmute` and every pointer coercion returned the operand unchanged;
- a write through a pointer into a caller's frame was dropped on return, and a
  pointer stored in a caller's local was resolved against the callee's locals;
- a `Deref` whose target was a pointer followed it a second time.

Known wrong answers that remain, because fixing them needs extractor data:

- `Drop` terminators only mark the local uninitialized; no drop glue runs, so
  a `Drop` impl that panics or exits is ignored;
- `Discriminant` returns the variant index, not a declared discriminant value.
