# F2 object-memory design

F2 defines one storage interface shared by the C and C++ lanes and available
to Rust. The normative C profile for this memory contract is GNU17 with the
C17 clauses and admitted GNU extensions listed in docs/c-tier-architecture.md.
The memory-relevant profile decisions
cover `realloc(p, 0)`, trap and non-value representations, indeterminate
values, `_BitInt`, packed and aligned members, zero-length arrays, `alloca`,
statement-expression temporaries, and GNU VLA behavior. TS 6010 and DR 260
govern the indeterminate and provenance choices. A profile records each
implementation-defined choice rather than allowing the evaluator to select a
convenient one.

## State and pointer values

The store is parameterized by a language instance L. Storage lifetime is
separate from language-level object lifetime. C++ placement construction,
transparent replacement, and `std::launder` can change the objects inhabiting
live storage without changing the allocation record.

    structure Store (L : Language) where
      allocs : L.AllocId -> Option (L.AllocState × Placement × List L.ByteState)
      exposed : Set L.AllocId
      nextId : L.AllocId

    structure Ptr (L : Language) where
      prov : Option (L.AllocId × L.Tag)
      addr : Nat

addr is the concrete address. An offset is derived from addr and the
placement of prov, so the representation has no redundant base and offset.
An empty-provenance pointer with a non-null address is permitted. Null is the
ABI null value with no provenance. A null value is never an allocation
placement.

An allocation record contains identity, kind, placement, size, alignment,
mutability, storage lifetime, exposure bit, and per-byte L.ByteState. Kinds include
static, automatic, allocated, literal, compound, and function storage. The
frontend supplies declaration identity, object size, alignment, array extent,
subobject offsets, flexible-array facts, padding, and bit-field facts. The
store never reconstructs those facts from a type spelling.

Allocation chooses an address in the allocation step. The choice is in the ABI
address range, nonzero, aligned for the request, and disjoint from every live
allocation. Null is the ABI null value and is never a placement. An invalid
choice is excluded from the relation rather than classified as undefined
behaviour. The step relation quantifies over every valid choice and also
admits the always-allowed outcomes where `malloc` or `calloc` returns null
because the request cannot be satisfied. Out of memory therefore has a
defined allocation-failure result, even when some valid placement exists.
`free` ends the allocation lifetime and invalidates every pointer carrying its
provenance. Any later use, including equality, ordering, subtraction, casts,
or a byte read, is undefined or a named refusal according to the profile.
`realloc` first ends the old allocation lifetime, then chooses a placement for
the new allocation in the same transition. Its result has a new allocation
identity even when the address is reused. The C profile records the
implementation-defined GNU behavior for `realloc(p, 0)` as an explicit
profile choice.

## Bytes and representation

The language-neutral byte lattice is

    uninit | byte(value, optional provenance)

There are no type tags on bytes. Integer, floating, pointer, function, and
padding representations are encoded as byte values with optional provenance.
A torn integer read is defined by decoding the available bytes according to
the profile representation. A pointer read requires a complete valid pointer
representation. Reading any object representation through a character lvalue
is defined, including pointer bytes, as required by C17 §6.5.1p7. A byte that
was only partly initialized is represented by the byte value produced by the
read-modify-write operation. The written bits come from the new value and the
unwritten bits come from the old byte when it is initialized. When the old
bits are padding or uninitialized, the relation chooses an allowed byte value
for those bits. A character read may observe the resulting initialized byte.
A typed read of an uninitialized or invalid representation follows the
profile's named indeterminate or non-value outcome.
Padding bytes and inactive union bytes receive an unspecified value where C17
§6.2.6.1p6-p7 permits one, and the step relation quantifies over every such
value.

memcpy copies bytes and their optional provenance, including effective-type
state, and overlapping copies are undefined under C17 §7.24.2.1p2. Every
non-character store updates effective type for affected bytes under C17
§6.5p6. It is not a first-store-only rule. Union stores and reads implement
active-member and common-initial-sequence rules of §6.5.2.3. Bit-field stores
perform read-modify-write on the storage unit and leave other bits at the
profile's permitted unspecified values. Flexible array members use the
remaining allocation extent. String literals are read-only, and literal
sharing is a quantified choice. Volatile accesses produce an ordered volatile
footprint and use a named refusal for unsupported external MMIO.

Uninitialized reads follow the GNU17 profile's explicit rule. Automatic and
allocated storage use named indeterminate outcomes, character observations use
the character exception, and register-object restrictions follow C17
§6.3.2.1p2. alloca, VLA, temporary, and static lifetimes are transitions in
allocation state. VLA lifetime starts at declaration, alloca lasts for the
function, and temporaries follow the GNU statement-expression profile.

## Pointer and integer conversions

Pointer/integer conversions use PNVI-ae-udi. A pointer-to-integer conversion
exposes the selected address and sets the allocation's exposed flag. A reverse
conversion may recover a live allocation only through the explicit exposure map
carried in the store or oracle record. Recovery derives the offset from the
allocation base, checks the target ABI alignment, and preserves the allocation
provenance. The exposure map and udi choice are explicit relation arguments.
The relation admits every allowed udi resolution, and the correctness theorem
quantifies over all of them. A raw integer carries no provenance or exposure
state and therefore does not fabricate an allocation identity. The ambiguous
one-past or adjacent-allocation recovery case is a named refusal under the
PNVI-ae profile. An empty-provenance non-null pointer remains a value, while
dereference requires live recovered provenance. Alignment failures are undefined under C23
§6.3.2.3p7. A non-null pointer with empty provenance is admitted only by a
profile that explicitly permits it, and dereference always requires recovered
live provenance.

## Operations, effects, and observations

The shared operation signature is:

    alloc : PlacementChoice -> AllocRequest -> Store L
            -> Result (AllocId × Store L × Footprint)
    dealloc : AllocId -> Store L -> Result (Unit × Store L)
    realloc : PlacementChoice -> AllocId -> AllocRequest -> Store L
              -> Result (Ptr L × Store L × Footprint)
    read : Access -> Store L -> Result (Value × Store L)
    write : Access -> Value -> Store L -> Result (Unit × Store L)
    copy : CopyAccess -> Store L -> Result (Unit × Store L)
    ptrOffset : Ptr L -> Int -> Store L -> Result (Ptr L × Store L)
    encode : Value -> Representation
    decode : AccessType -> Representation -> Result Value

Every operation returns a defined result, classified undefined behavior, or a
named unsupported refusal. Placement choices, allocation failure, padding,
unspecified bytes, literal sharing, evaluation order, and PNVI exposure are
explicit arguments or universally quantified choices. Each memory operation
returns a footprint containing allocation identity, byte range, access kind,
and sequencing information for later control-flow semantics. The allocation,
deallocation, and exposure choices are arguments to the relation or its oracle
record, so a caller cannot hide a placement decision in evaluator fuel or in
a host-side global.

Allocation, deallocation, reallocation, and address exposure are internal
steps, not observable events. Observables are volatile accesses ordered by
C17 §5.1.2.3p6, external I/O calls, exit status, divergence, and the
undefined-behavior outcome. The compiler-correctness theorem therefore
allows an unused allocation/free pair to disappear. External-call events are
the observable boundary and carry footprints rather than host addresses.


## Language interface and hooks

The shared interface is parameterized by a language record rather than a
second store implementation:

    structure Language where
      AllocId : Type
      Tag : Type
      ByteState : Type
      AllocState : Type
      onAlloc : AllocRequest -> AllocState -> AllocState
      onRead : Access -> AllocState -> Result Unit
      onWrite : Access -> Value -> AllocState -> Result AllocState
      onCopy : CopyAccess -> AllocState -> Result AllocState
      onDealloc : AllocId -> AllocState -> Result AllocState
      onRetag : Access -> AllocState -> Result AllocState

C instantiates the hooks with declared/effective type and C lifetime state. C++
adds active union members, subobjects, pointer-interconvertibility and
temporary lifetime. Rust supplies borrow tags and per-location alias state.
Every hook receives the allocation and byte footprint relevant to the event,
and every refusal is part of the shared result type.

## GNU17 decision table

| Decision | Profile rule | Contract
| --- | --- | --- |
| pointer/integer provenance | PNVI-ae-udi | exposure map is explicit, ambiguous one-past recovery refuses |
| `realloc(p, 0)` | GNU17 implementation-defined behavior | profile parameter, with old lifetime ending before a successful replacement |
| effective type | C17 §6.5p6-p7 | every non-character store updates affected allocated bytes, character stores do not retype |
| union access | C17 §6.5.2.3p3 | bytes are reinterpreted through the selected member and common-initial-sequence rules |
| uninitialized lvalue read | C17 §6.3.2.1p2 | undefined or named refusal according to storage duration and representation |
| character observation | C17 §6.5.1p7 | unsigned-character reads are defined and quantify unspecified byte values |
| pointer alignment | C23 §6.3.2.3p7 | invalid alignment is undefined behavior |
| allocation failure | GNU17 allocator profile | null result is an allowed defined outcome |

## Address independence and refinement

Let rho1 and rho2 be placement resolutions for the same initial objects,
inputs, and nondeterministic choices. A per-allocation renaming R preserves
provenance, byte offsets, object sizes, alignments, liveness, and disjointness
while changing one selected live allocation's base address. The step relation
is renamed operation by operation, and the relation is lifted to behavior
sets:

    address_independent :
      R w1 w2 ->
      Behaviors program w1 = renameBehaviors R (Behaviors program w2)

The theorem applies to a per-allocation move when the program does not observe
that allocation's address. Its exceptions are one-past-the-end equality,
alignment undefined behavior on casts, and integer reads of pointer bytes. A
removal lemma permits an allocation and its matching deallocation to disappear
when no observable footprint or later live pointer depends on them. The relation
also covers values retained in registers and overlapping storage by requiring
the same source allocation and lifetime state on both sides.
Programs that observe addresses are proved for every admissible placement and
exposure resolution. The flat-memory refinement is an XLEN-parameterized
forward simulation. It maps each live allocation to its chosen interval and
maps an abstract byte to its concrete value while forgetting optional
provenance. Every defined abstract step is matched by a flat-memory step with
the same observable footprint and termination result. An abstract
undefined-behavior step carries no refinement obligation. An abstract
uninitialized byte is related to every concrete byte value permitted by the
profile, and a dead allocation's interval may be reused after its lifetime
ends. Provenance checks therefore remain source-side obligations of the
abstract relation rather than properties of the flat target state.

## Language parameter and migration

L.Tag, L.ByteState, and L.AllocState are language parameters. The alias
instance supplies onAlloc, onRead, onWrite, onCopy, onDealloc, and onRetag
hooks, with state allowed at each byte and allocation rather than in one
stateless predicate. C uses effective type and C lifetime state. C++ adds the object tree,
active union member, pointer-interconvertibility, subobject and vtable
allocations, and temporary lifetime. Rust supplies borrow tags and
per-location Stacked Borrows or Tree Borrows state through the same hooks. The
current stateless C++ AliasModel and the Rust store are migration debt. C and
C++ object stores converge on this interface before their independent layers
are retired. The current C++ `AliasModel`, `Cpp/ObjectModel`, and Rust store
are migration debt. C is ported first, then C++ subobjects and active-union
state move to the language hooks. `Cpp/ObjectModel` is removed only after its
callers use the shared operations and replacement rows cover the same cases.

The F2 gates are S1 structured types with zero type-string operations and a
rerunnable survey, S2 well-formedness preservation for every exported memory
operation plus at least 25 differential rows under native-placement replay,
and S3 a proved address_independent evaluator theorem with verdicts for all
effective-type and pointer/integer rows.
