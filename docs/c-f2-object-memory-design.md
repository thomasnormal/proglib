# F2 object-memory design

F2 defines one storage interface shared by the C and C++ lanes and available
to Rust. The normative C profile is GNU17, meaning C17 plus the admitted GNU
extensions listed in docs/c-tier-architecture.md. C23/N3220 clause numbers are
cited where they describe the same rule. The memory-relevant profile decisions
cover realloc(p, 0), trap and non-value representations, indeterminate values,
_BitInt, packed and aligned members, zero-length arrays, alloca, statement-
expression temporaries, and GNU VLA behavior. TS 6010 and DR 260 govern the
indeterminate and provenance choices.

## State and pointer values

The store is parameterized by a language instance L:

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
mutability, lifetime, exposure bit, and per-byte L.ByteState. Kinds include
static, automatic, allocated, literal, compound, and function storage. The
frontend supplies declaration identity, object size, alignment, array extent,
subobject offsets, flexible-array facts, padding, and bit-field facts. The
store never reconstructs those facts from a type spelling.

Allocation chooses an address in the allocation step. The choice is in the ABI
address range, nonzero, aligned, and disjoint from every live allocation. The
step relation quantifies over every valid choice and admits allocation failure
and out-of-memory outcomes. free ends the allocation lifetime and invalidates
every pointer carrying its provenance. Any later use, including equality,
ordering, subtraction, casts, or a byte read, is undefined or a named refusal
according to the profile. realloc first deallocates the old object, then
chooses a placement for the new object. GNU17 realloc(p, 0) is an
implementation-defined profile choice.

## Bytes and representation

The language-neutral byte lattice is

    uninit | byte(value, optional provenance)

There are no type tags on bytes. Integer, floating, pointer, function, and
padding representations are encoded as byte values with optional provenance.
A torn integer read is defined by decoding the available bytes according to
the profile representation. A pointer read requires a complete valid pointer
representation. Reading any object representation through a character lvalue
is defined, including pointer bytes, as required by C17 §6.5.1p7. A byte that
was only partly initialized is handled by the byte lattice. A character read
may observe its initialized value. A typed read of an uninitialized or invalid
representation follows the profile's named indeterminate or non-value outcome.
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
conversion recovers the corresponding live provenance only when the PNVI
recovery rule permits it and the integer has the required ABI alignment. An
integer with no exposed allocation is not assigned fabricated provenance. The
exposed flag, recovery relation, and implementation's undefined-integer choice
are explicit state. Rule 4 quantifies universally over every admissible
exposure and recovery choice. Alignment failures are undefined under C17
§6.3.2.3p7.

## Operations, effects, and observations

The shared operation signature is:

    alloc : PlacementChoice -> AllocRequest -> Store L
            -> Result (AllocId × Store L)
    dealloc : AllocId -> Store L -> Result (Unit × Store L)
    realloc : PlacementChoice -> AllocId -> AllocRequest -> Store L
              -> Result (Ptr L × Store L)
    read : Access -> Store L -> Result (Value × Store L)
    write : Access -> Value -> Store L -> Result (Unit × Store L)
    copy : CopyAccess -> Store L -> Result (Unit × Store L)
    ptrOffset : Ptr L -> Int -> Store L -> Result (Ptr L × Store L)
    encode : Value -> Representation
    decode : AccessType -> Representation -> Result Value

Every operation returns a defined result, classified undefined behavior, or a
named unsupported refusal. Placement choices, allocation failure, padding,
unspecified bytes, literal sharing, evaluation order, and PNVI exposure are
explicit arguments or universally quantified choices. Each read and write
returns a footprint containing allocation identity, byte range, access kind,
and sequencing information for later control-flow semantics.

Allocation, deallocation, reallocation, and address exposure are internal
steps, not observable events. Observables are external I/O calls, exit status,
and the undefined-behavior outcome. The compiler-correctness theorem therefore
allows an unused allocation/free pair to disappear. External-call events are
the observable boundary and carry footprints rather than host addresses.

## Address independence and refinement

Let rho1 and rho2 be placement resolutions for the same initial objects,
inputs, and nondeterministic choices. A per-allocation renaming R preserves
provenance, byte offsets, object sizes, alignments, liveness, and disjointness
while changing each selected base address. Address independence is relational
over behavior sets:

    address_independent :
      R w1 w2 ->
      Behaviors program w1 = renameBehaviors R (Behaviors program w2)

The theorem applies to programs with no address observation. Its exceptions are
one-past-the-end equality, alignment undefined behavior on casts, and integer
reads of pointer bytes. Programs that observe addresses are proved for every
admissible placement and exposure resolution. The flat-memory refinement maps
each live allocation to its chosen interval and preserves bytes, provenance
failures, classified undefined behavior, and footprints. Undefined source
behavior carries no compiler-refinement obligation.

## Language parameter and migration

L.Tag, L.ByteState, and L.AllocState are language parameters. The alias
instance supplies onAlloc, onRead, onWrite, onCopy, onDealloc, and onRetag
hooks. C uses effective type and C lifetime state. C++ adds the object tree,
active union member, pointer-interconvertibility, subobject and vtable
allocations, and temporary lifetime. Rust supplies borrow tags and
per-location Stacked Borrows or Tree Borrows state through the same hooks. The
current stateless C++ AliasModel and the Rust store are migration debt. C and
C++ object stores converge on this interface before their independent layers
are retired.

The F2 gates are S1 structured types with zero type-string operations and a
rerunnable survey, S2 well-formedness preservation for every exported memory
operation plus at least 25 differential rows under native-placement replay,
and S3 a proved address_independent evaluator theorem with verdicts for all
effective-type and pointer/integer rows.
