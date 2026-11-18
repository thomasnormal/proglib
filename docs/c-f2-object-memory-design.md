# F2 object-memory design

This design makes the C object store the shared memory interface for C++ and
Rust. The C semantics keeps the ISO C23 rules for lifetime, bounds, effective
type, representations, and pointer conversions. Rust supplies the same core
through the MIR memory boundary described in `docs/rust-design.md`.

## Values and allocation choices

A pointer is a pair of allocation provenance and concrete address, followed by
an offset and an optional subobject bound. Provenance identifies the allocation
and offset. The address is the chosen base address plus the offset. A null
pointer has no provenance. An allocation records its stable identity, address,
size, alignment, byte cells, lifetime, and mutability. Allocation chooses an
address from the set of aligned, non-overlapping placements allowed by the ABI.
The choice is part of the execution world and stays fixed for the allocation's
lifetime. Reallocation creates a new identity when the standard permits the
object to move. A pointer-to-integer conversion observes the chosen address
only through an explicit exposure operation. Integer-to-pointer recovery keeps
the exposure and provenance checks visible in the semantics.

The abstract store does not use host pointers. Its byte cell is one of
uninitialized data, an integer byte, a floating byte, or a pointer fragment
with provenance. Reads and writes operate on byte ranges after checking
lifetime, bounds, alignment, initialization, representation validity, and the
aliasing instance. Layout facts arrive from the approved Clang or rustc
frontend. The store never reconstructs size or alignment from a type spelling.
An absent layout or unsupported byte representation is a named refusal before
any bytes are guessed.

## Aliasing and language instances

Memory operations take an `AliasModel` parameter. The C instance checks the
declared effective type rules in C23 §6.5.1p6-p7, including compatible types,
qualified and signed variants, aggregate members, and character accesses. The
allocated-storage case records the first non-character store as the effective
type. Aggregate objects retain per-member declaration facts instead of stamping
the enclosing object with one member's type. A C++ instance can add active
member and lifetime rules while using the same bytes and pointer interface.
Rust Slice 1 uses strict provenance with lifetime, layout, initialization,
alignment, and validity checks. It deliberately leaves Stacked Borrows and
Tree Borrows outside the base instance. Rust rows are admitted only when both
borrow-model oracle runs agree. A later alias instance can strengthen the
checks without changing allocation, pointer, or byte definitions.

## Address independence

The ordinary theorem surface should hide concrete addresses. Define an
address-renaming relation that changes every live allocation's chosen base and
the address component of its pointers while preserving provenance, offsets,
bounds, disjointness, and alignment. The central lemma is

```text
address_independent :
  address_renaming w w' →
  run abi alias program w = run abi alias program w'
```

for programs whose observable operations do not expose an address. The
relation is lifted over traces and terminal outcomes. Programs that compare,
store, print, or cast an address use the explicit exposure semantics and are
proved against every admissible address choice. This keeps ordinary C proofs
free of arbitrary numeric placements while retaining the choices required by
PNVI-ae-udi and by Rust strict provenance.

The abstract-to-flat refinement maps each live allocation to its selected
address interval. It proves that byte reads, writes, pointer arithmetic,
allocation footprints, and exposed casts agree with the flat representation.
The refinement preserves provenance failures and classified undefined behavior
as well as defined values.

## Required operations and Rust handoff

The shared interface consists of `alloc`, `dealloc`, `realloc`, `read`,
`write`, `copy`, `ptr_offset`, `encode`, `decode`, pointer exposure, and
provenance recovery. Each operation returns a defined result, a classified
undefined-behavior outcome, or a named unsupported refusal. The event layer
records allocation, deallocation, reallocation, volatile access, external
calls, and address exposure with allocation identities rather than host
addresses.

The current C `Mem` already separates `Ptr.obj` from `Ptr.address`, tracks
placements, and has address-renaming lemmas for core accesses. F2 completes
that interface by making placement validity an allocation invariant, routing
all casts through exposure and recovery, and proving the address-independence
lemma over evaluator runs. The Rust lane needs the same allocation and byte
contracts for `StorageLive`, `StorageDead`, MIR places and projections, enum
layout, pointer fragments, and Miri's strict-provenance outcomes. A change to
these shared definitions is an architecture change and requires both C and
Rust differential rows.
