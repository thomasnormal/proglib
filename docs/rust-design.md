# Rust MIR design for Slice 1

This document is the design companion to
[`rust-stage0.md`](rust-stage0.md). It specifies the semantic interface before
Lean implementation begins. The approved input is the self-contained
`rustc_public` envelope emitted by the pinned nightly, containing the
Runtime(Optimized) bodies Miri executes. Rustc's lowering to those bodies is a
trusted, named boundary for this lane: match compilation, drop elaboration,
closure lowering, and the async state transform are not reimplemented by the
envelope loader.

The design follows the shared roadmap constraints 1.1--1.5: behaviours are
traces of observable events, open choices are quantified, and all external
operations use one registry. Rust has no normative operational semantics, so
the clause source for memory and MIR-like execution is MiniRust at commit
`063d784` (dual Apache-2.0/MIT licence); this document summarizes its
interfaces rather than copying its source. Where the pinned Miri behaviour is
the oracle, the exact nightly and Miri flags remain part of the theorem's
assumptions.

## Configurations and behaviours

A program is an envelope plus its entry instance. A machine configuration has
these components:

| component | role |
|---|---|
| `stack` | Call frames, from the entry frame to the current frame. |
| `frame` | Monomorphic instance, body id, basic-block/statement program counter, locals, return destination, and normal/unwind continuations. |
| `memory` | Allocations, bytes, provenance, lifetimes, layouts, and the address choice for each allocation. |
| `globals` | Static, vtable, function and constant allocations from the envelope. |
| `world` | ABI parameters, external registry, intrinsic state, clock/OS state, and the choice witnesses for open operations. |
| `trace` | The observable event prefix produced so far. |

The defining judgement is a labelled transition relation:

```text
step (abi, registry) : Config -> Event × Config  +  Terminal
```

A run is a finite or infinite sequence of these steps. `Behaviours p` is the
set of maximal traces and terminal observations permitted by the relation for
program `p`, for every admissible initial state, external input, address
choice, and other open choice. A derived runner may search for a finite
terminal result, but the big-step runner is not the definition. Divergence is
an infinite behaviour; it is not silently converted to timeout or success.

The terminal observations are `return value`, process `exit status`,
`panic` (including its unwind trace), `ub` with a classified cause, and a
named `unsupported` refusal. An incomplete or timed-out search is not a
behaviour and establishes no theorem. A semantic theorem therefore has the
shape “every behaviour of the MIR program is permitted by the specification”
and retains correlations between choices made at different steps.

The pinned target supplies one ABI record for the ordinary lane runs (pointer
width, endianness, integer widths, alignment and `char` representation). The
transition relation still takes the record explicitly, so a later target has a
new parameter rather than a second semantics. If the Rust implementation leaves
a choice open, its oracle is a value in `world` and the behaviour set
quantifies over all values allowed by the ABI or external contract. MIR's
specified destination/function/argument evaluation order is followed exactly;
there is no convenient source-level evaluation order hidden in the runner.

## Observable events

Events are the interface between a MIR execution and a specification. Internal
assignments and control-flow edges do not become observable events. The initial
registry has these event families:

| event | payload |
|---|---|
| `call_external` | registry key, typed arguments, pre-state footprint, and the returned outcome or UB. |
| `volatile_read` / `volatile_write` | allocation/provenance, byte range, and encoded value. |
| `allocate` / `deallocate` / `reallocate` | requested layout, chosen concrete address, allocation id, and result. |
| `stdout` | exact byte sequence, when the later formatting/printing slice admits it. |
| `panic` | panic payload/entry and the cleanup path; the normal process status is 101. |
| `exit` | status code. |
| `ub` | the classified validity, bounds, initialization, alignment, lifetime, provenance or arithmetic fault. |

A registry operation emits its event at the boundary and then returns a
relation of possible post-states. A pure MIR call has no external event; its
body's events remain in the enclosing trace. Event payloads use typed values
and allocation identities, not host pointers or pretty-printed source text.
The trace is therefore suitable for differential comparison with Miri and for
refinement to a flat machine trace later.

Slice 1 is single-threaded. There is no scheduler choice in that slice, and
atomics, data races, thread-local state, files, clocks, and stdout formatting
are named later boundaries. Adding one later must extend `Event` and the
registry, not change the meaning of existing events.

## Memory interface

The memory interface has an abstract view and a concrete-address refinement.
An allocation is a record

```text
Allocation = {
  id          : AllocationId,
  address     : Address,
  size        : Nat,
  align       : Nat,
  bytes       : Array ByteCell,
  provenance  : Array (offset, allocation-id),
  lifetime    : Live | Dead,
  mutability  : Immutable | Mutable
}
```

`ByteCell` carries its initialization state and, where a pointer fragment is
stored, its provenance. A pointer value carries an allocation id and offset;
it is not just an integer. The `AddressChoice` component of `world` chooses a
non-overlapping concrete address for each allocation, subject to the ABI's
alignment and address-space constraints. The same allocation keeps the same
choice for its lifetime. Correctness quantifies over every admissible address
assignment, so a proof cannot rely on a lucky numeric address.

The primitive operations are `alloc`, `dealloc`, `read`, `write`, `copy`,
`ptr_offset`, `encode`, and `decode`. `encode` and `decode` use the rustc
layout table in the envelope, including enum discriminant and niche data;
they check size, alignment, initialization and validity. `StorageLive` and
`StorageDead` update local lifetime state. A read, write, drop, invalid cast or
invalid decode yields a distinguished `ub` outcome with its cause. A missing
layout or unsupported representation yields a named refusal before any bytes
are guessed.

Slice 1 uses strict provenance and no Stacked Borrows or Tree Borrows rule.
That memory instance is a deliberate permissive base: it checks lifetime,
layout, alignment, initialization and provenance but adds no aliasing policy.
An admissible oracle row must nevertheless produce a defined result under
both `-Zmiri-tree-borrows` and default Stacked Borrows. Tree Borrows can later
be supplied as another `AliasModel` instance without changing the transition
relation. Rows where the two models disagree are excluded from Slice 1 claims.

The abstract-to-flat refinement maps every live allocation to its chosen
address interval and proves that byte reads/writes, pointer arithmetic and
external footprints agree. Pointer-to-integer and integer-to-pointer casts are
the explicit meeting point: strict-provenance casts preserve an allocation
identity, while an exposed-provenance operation is a later named extension.
This interface is intended to be shared with the C lane's F2 object memory;
any change to that shared core is a request to the C lane and the lead, not a
local Rust rewrite.

## MIR execution and calls

The loader preserves statement, terminator, rvalue, operand, projection,
constant, layout, span and debug-info nodes one for one. The interpreter has a
case for each supported Runtime(Optimized) node. `Assign` evaluates its rvalue
and writes the destination; storage markers update lifetime; `SwitchInt`,
`Goto`, `Return`, `Call`, `Drop`, `Assert` and cleanup terminators advance the
frame or its unwind continuation. A `Call` first evaluates its destination,
then function operand, then arguments in the pinned MIR order, and transfers
ownership according to `Copy`/`Move`.

A direct call uses the resolved monomorphic instance id in the envelope. A
function pointer or virtual call is resolved only when the envelope contains a
structured target (for example a vtable slot); otherwise it produces an
`unsupported(indirect-call)` outcome. The loader never scans source text to
recover a callee. Intrinsics are handled by the same registry interface as
foreign operations, with their typed preconditions and result relation.

The standard library is executed from its encoded MIR. The initial foreign
registry contains only the allocator family (`__rust_alloc`,
`__rust_alloc_zeroed`, `__rust_realloc`, `__rust_dealloc`), process termination
(`exit`, `abort`), and the panic entry point. `write` and formatting are
admitted only in the later stdout slice. A foreign function without a registry
entry is a named refusal, not a no-op.

## Externals and proved standard-library lemmas

There is one registry for foreign functions, intrinsics, and reusable
standard-library contracts:

```text
ExternalSpec = {
  key       : StableSymbol,
  signature : LayoutSignature,
  pre       : World -> Args -> Prop,
  post      : World -> Args -> Result -> World -> Prop,
  events    : World -> Args -> Result -> List Event,
  failure   : World -> Args -> FailureClass
}
```

The key contains the envelope's stable instance/fingerprint and ABI signature;
a short source name is only a display label. `pre` and `post` mention the
abstract memory and event payloads. A spec may permit several post-states,
but every permitted outcome must satisfy the contract. The registry records
whether an entry is a trusted foreign shim, an executable intrinsic rule, or a
proved MIR lemma. Trusted entries are listed in the lane's audit; they are not
axioms about Rust functions whose MIR is available.

A proved standard-library lemma is registered only after a theorem relates the
actual monomorphic body (and its resolved callees) to the `ExternalSpec`:

```text
 theorem std_lemma_sound :
   RefinesBody envelope instance_id registry_spec := ...
```

The registry stores the theorem name, source/body fingerprint, pinned nightly,
and the proof's dependency list. A call may use the lemma as a derived
refinement rule to avoid re-walking a body in a client proof, while the
operational semantics still runs the real MIR. If a body or layout fingerprint
changes on re-pin, the registration becomes stale and the theorem must be
reproved. There is no attribute that silently turns an unproved contract into
semantics.

## Source-facing goals

The semantic state is MIR-shaped, but proof goals should be readable in Rust
terms when the envelope provides enough provenance. Each program point carries
a `SpanId`; the span table records file, start/end line and column, and a
compiler diagnostic display. Each body also retains rustc's `var_debug_info`,
which maps MIR locals and projections to source variable names and value
fragments. The pretty-printer uses those tables to render:

- a frame as `function_name` with its monomorphic type arguments;
- locals and projections by their debug names, with the MIR local id retained
  when a name is ambiguous or has gone out of scope;
- a block/statement position as `file:line:column` plus the stable body and
  block id;
- values through the rustc layout/type table, never by decoding arbitrary bytes
  as a guessed Rust type.

A displayed goal therefore has a source-facing header and an exact MIR
breadcrumb, for example “`gcd` at `gcd.rs:12:9`, body `…`, block 4, before
`SwitchInt`”. The header is presentation only: theorem statements refer to the
stable envelope ids, spans and typed locals. If debug information does not
identify a source term, the printer shows the MIR place and reports that no
source name is available; it does not invent a name or reparse the `.rs` file.
This keeps source display useful while making the trusted lowering boundary
explicit.

## Proof and differential obligations

For each supported node family, the implementation gets three companion
artifacts: its transition equation, an oracle row against the pinned Miri
under both borrow models, and a proof that the event/terminal observation is
preserved by any registered refinement. The differential runner compares event
prefixes and terminal classes, not merely a final integer. It records a named
refusal when extraction, layout, call resolution or the memory instance is
outside the slice.

The first proof examples are the integer gcd loop, a `Vec` sum through
`slice::Iter`, and an enum match. Their invariants are stated over the MIR
frames and memory representation; the source-facing printer supplies the
names and spans used by a human. A later VC layer may derive source-level
contracts, but it must refine this transition system rather than replace it.

The pinned inputs and the Stage 0 report are part of every result: nightly
`2026-11-16`, rustc revision `5f4effd579500175af844241eb179e756190f1e7`,
Miri revision `5f4effd579`, Miri's Runtime(Optimized) flags, and MiniRust
`063d784`. Re-pinning requires a syntax/validator diff, a fresh envelope and
oracle census, and rechecking all registered lemma fingerprints.
