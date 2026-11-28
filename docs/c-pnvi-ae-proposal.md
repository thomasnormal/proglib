# PNVI-ae pointer and integer representation proposal

**PNVI PROPOSAL READY**

This proposal records the contract for the future pointer/integer and
pointer-byte family. It does not change the current evaluator. The current
frontier remains loud refusal.

## Corpus need

The current dynamic survey has 12 sole rows whose first refusal is
`isolated non-null integer-to-pointer cast requires PNVI-ae exposure and
recovery`, and one sole row whose first refusal is
`pointer byte read requires an address placement oracle`. The family map
counts 14 pointer-to-integer rows and 13 integer-to-pointer rows in the
broader corpus, alongside 24 effective-type bit-cast rows. The focused
harness has ten registered pointer/integer or pointer-byte rows. These counts
are walls, not a claim that all rows become admitted together. Layout,
effective type, and byte initialization remain independent prerequisites.

## State and representation

The C instance uses a pointer value

```
Ptr := null | live(object : ObjId, address : Nat, offset : Int, bound : Option Int)
```

and a byte value

```
CByte := concrete(UInt8) | indeterminate | pointerByte(Ptr, fragment : Nat)
        | pointerIntegerByte(Ptr, fragment : Nat)
```

The allocation store records object lifetime, declared/effective type by
byte, initialized state, and the chosen address. Provenance is the `ObjId`
inside `Ptr`, never an address reconstructed from a type spelling. A pointer
stored in an aggregate is encoded as pointer fragments, so a load preserves
the same provenance token. `fragment` is the byte index in the profile's
little-endian pointer representation. Reading a pointer's bytes through an
unsigned-character lvalue is a defined byte observation under C23 §6.2.6.1p4
and §6.5.2.3p3, subject to the profile's representation choice. A pointer
byte read through a non-character lvalue remains a non-value or effective-type
refusal.

## PNVI-ae rules

The chosen model is PNVI-ae. A pointer-to-integer cast in C23 §6.3.2.3p6
exposes the pointer's address and records its provenance in the execution
state. A non-pointer read of bytes carrying pointer provenance also exposes
those bytes before producing an integer. I/O that publishes the pointer value
is an exposure event under the same rule. An integer-to-pointer cast in
§6.3.2.3p5 recovers a live object only when the integer is the exact exposed
address recorded for that object, with an offset in the object's permitted
range. A null integer recovers the profile's null pointer. A non-null integer
without a matching exposure refuses. A pointer loaded from pointer fragments
keeps the fragment's provenance and does not perform a fresh address lookup.

Pointer equality in §6.5.9 with equal addresses and different provenance is a
language hook. The C profile records its allowed result set. The adjacent
one-past and different-object case that PNVI-ae-udi leaves ambiguous is a
named refusal in this tier, never a convenient Boolean choice. Pointer
ordering and difference retain their existing array-provenance checks.

Allocation, free, and address exposure are not observables. The observables
are volatile accesses, I/O calls, termination status, and divergence. An
allocation may choose any unused aligned address, and the choice is threaded
through the step relation. Null is never a placement. Allocation failure and
out-of-memory are allowed outcomes. A removed allocation is matched by the
source resolution that takes its failure branch, while a target run may end
in exhaustion after the common observable prefix.

## Nondeterminism and proof obligations

The address choice, pointer-equality choice supplied by the profile, and
indeterminate unsigned-character byte values are explicit oracle arguments.
The semantics quantifies over every admissible choice. A theorem may use a
cheap sufficient condition such as a known allocation address or a known
byte, but it may not select one resolution silently. Every memory operation
returns a footprint containing reads, writes, exposure, and possible faults.
The address-independence theorem compares two runs that agree on exposed
allocations and permits per-allocation renaming. Its exceptions are
one-past equality, alignment UB on casts (C23 §6.3.2.3p7), and observations
that read pointer bytes as integers. The current evaluator does not claim
this theorem and therefore keeps the corresponding rows refused.

Implementation begins only after the owner accepts this contract and the
shared byte store is available. Until then, `ptrInt`, pointer-byte loads,
arbitrary integer-to-pointer casts, and unresolved provenance comparisons
remain loud refusals. No source transformation or address choice is allowed
to make a row pass.
