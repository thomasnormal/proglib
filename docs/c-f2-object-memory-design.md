# F2 object memory

C and C++ share one store. Rust can supply its alias and lifetime rules
through the same interface. The C memory profile is GNU17, meaning ISO/IEC
9899:2018 plus the GNU extensions listed below. All unqualified C clause
numbers in this document refer to that edition. Provenance follows the
PNVI-ae variant of WG14 N2364 and the exposure rules described in N2362.
The public TS 6010 working draft and DR 260 provide the provenance
and lifetime background. The profile decisions below govern cases where
the TS uses user disambiguation or a different boundary rule. [N2362], [N2364], [TS 6010], [DR 260]

## Store and transition interface

An allocation owns storage. Its language metadata can describe several
objects with distinct lifetimes in that storage. Each allocation ID is
fresh, including after address reuse. A dead allocation retains its identity
for liveness checks. Byte and location-state arrays have equal length.
Layout, subobject identities, access types, size and alignment come from
canonical Clang types and same-invocation declaration identities.

The types below specify the interface for S2. Each operation takes
its request, its choices, and its input store. An inadmissible choice yields
`none` and contributes no transition. A legal request and choice produce a
step, which can succeed, report resource exhaustion, classify undefined
behavior, or refuse a named case. Every step carries its storage footprint.

```lean
namespace F2

abbrev AllocId := Nat

structure Provenance (Tag : Type) where
  storage : AllocId
  tag : Tag

inductive Byte (Tag : Type) where
  | uninit
  | byte (value : UInt8) (provenance : Option (Provenance Tag))
      (fragment : Option Nat)

structure Ptr (Tag : Type) where
  provenance : Option (Provenance Tag)
  address : Nat

structure LanguageTypes where
  Tag : Type
  CanonType : Type
  Value : Type
  AllocationState : Type
  LocationState : Type
  HookChoice : Type
  RetagRequest : Type
  ObjectLifetimeRequest : Type
  Fault : Type

namespace CInstance

inductive Tag where
  | object (allocation : AllocId)
  | function (symbol : Nat)

inductive CanonType where
  | void | integer (signed : Bool) (bits : Nat) | floating (bits : Nat)
  | pointer (pointee : CanonType) | aggregate (declaration : Nat)

inductive AllocationState where
  | reserved | live | ended

inductive EffectiveTypeState where
  | untyped | typed (type : CanonType) | padding | indeterminate

structure LocationState where
  effectiveType : EffectiveTypeState
  initialized : Bool

inductive HookChoice where
  | default
  | placement (site : Nat)
  | unspecified (site : Nat)

inductive Fault where
  | outOfBounds | lifetimeEnded | alignment | invalidRepresentation
  | effectiveType | indeterminateRead | ambiguousRecovery

inductive Value where
  | integer (value : Int)
  | bytes (value : Array (Byte Tag))

def types : LanguageTypes :=
  { Tag := Tag
    CanonType := CanonType
    Value := Value
    AllocationState := AllocationState
    LocationState := LocationState
    HookChoice := HookChoice
    RetagRequest := Unit
    ObjectLifetimeRequest := Unit
    Fault := Fault }

end CInstance

inductive StorageKind where
  | staticStorage | threadLocal | automatic | heap | literal | function | vtable

inductive LifetimeEnd where
  | process | thread (id : Nat) | block (scope : Nat) | function (frame : Nat)
  | fullExpression (evaluation : Nat) | free | replace

inductive InitialContents where
  | uninitialized | zeroBytes | typedZero

structure Metadata (T : LanguageTypes) where
  allocationState : T.AllocationState
  locations : Array T.LocationState

structure Allocation (T : LanguageTypes) where
  kind : StorageKind
  lifetimeEnd : LifetimeEnd
  base : Option Nat
  alignment : Nat
  live : Bool
  writable : Bool
  exposed : Bool
  bytes : Array (Byte T.Tag)
  metadata : Metadata T

structure Store (T : LanguageTypes) where
  allocations : List (AllocId × Allocation T)
  nextId : AllocId

structure ByteRange where
  first : Nat
  length : Nat

structure ABI (T : LanguageTypes) where
  addressBits : Nat
  usableRanges : List ByteRange
  nullAddress : Nat
  typeLayout : T.CanonType → Option (Nat × Nat)
  encodeAddress : T.CanonType → Nat → Option (Array UInt8)
  decodeAddress : T.CanonType → Array UInt8 → Option Nat
  encodeValue : T.CanonType → T.Value → Option (Array (Byte T.Tag))
  decodeValue : T.CanonType → Array (Byte T.Tag) → Option T.Value
  pointerToInteger : T.CanonType → Nat → Option Int
  integerToAddress : T.CanonType → T.CanonType → Int → Option Nat

structure Region where
  storage : AllocId
  bytes : ByteRange

inductive AccessKind where
  | readBytes | writeBytes | readMetadata | writeMetadata

structure Footprint where
  locations : List (AccessKind × Region)
  starts : List AllocId
  ends : List AllocId
  exposes : List AllocId

inductive Designator (Tag : Type) where
  | indirect (pointer : Ptr Tag)
  | direct (provenance : Provenance Tag) (offset : Nat)

structure Access (T : LanguageTypes) where
  target : Designator T.Tag
  type : T.CanonType
  width : Nat
  alignment : Nat
  isVolatile : Bool
  packedMember : Bool

inductive CopyKind where
  | memcpy | memmove | characterArrayCopy

structure CopyRequest (T : LanguageTypes) where
  source : Designator T.Tag
  destination : Designator T.Tag
  length : Nat
  kind : CopyKind

structure AllocRequest (T : LanguageTypes) where
  kind : StorageKind
  lifetimeEnd : LifetimeEnd
  size : Nat
  alignment : Nat
  addressable : Bool
  writable : Bool
  declaredType : Option T.CanonType
  initialContents : InitialContents

inductive PlacementChoice where
  | address (base : Nat)
  | unaddressable
  | fail

inductive LiteralChoice where
  | separate (placement : PlacementChoice)
  | share (region : Region)

structure ByteChoices where
  values : List UInt8

structure AccessChoices (T : LanguageTypes) where
  bytes : ByteChoices
  hook : T.HookChoice

structure ReallocChoices (T : LanguageTypes) where
  placement : PlacementChoice
  endHook : T.HookChoice
  allocHook : T.HookChoice
  copyHook : T.HookChoice

inductive BoundaryChoice where
  | ordinary | adjacent | separate

inductive EqualityChoice where
  | equal | unequal

inductive OrderingTest where
  | lt | le | gt | ge

inductive OutputExposure (Tag : Type) where
  | pointerFormat (pointer : Ptr Tag)
  | representation (regions : List Region)

inductive Failure (T : LanguageTypes) where
  | ub (fault : T.Fault)
  | unsupported (name : String)
  | exhausted (kind : StorageKind)

structure HookResult (T : LanguageTypes) (A : Type) where
  result : Except (Failure T) A
  updates : List (AllocId × Metadata T)
  locations : List (AccessKind × Region)

structure Hooks (T : LanguageTypes) where
  onAlloc : Store T → AllocId → AllocRequest T → T.HookChoice →
    HookResult T (Metadata T × T.Tag)
  onRead : Store T → Access T → Region → T.HookChoice → HookResult T Unit
  onWrite : Store T → Access T → Region → T.Value → T.HookChoice → HookResult T Unit
  onCopy : Store T → Store T → CopyRequest T → Region → Region → T.HookChoice →
    HookResult T Unit
  onDealloc : Store T → AllocId → LifetimeEnd → Option (Provenance T.Tag) → T.HookChoice →
    HookResult T Unit
  onRetag : Store T → Region → Provenance T.Tag → T.RetagRequest → T.HookChoice →
    HookResult T T.Tag
  onObjectLifetime : Store T → Region → T.ObjectLifetimeRequest → T.HookChoice →
    HookResult T Unit
  recoveredTag : Store T → AllocId → Nat → T.CanonType → Option T.Tag

inductive RecoveryPolicy where
  | pnviAe | strict

structure Language where
  types : LanguageTypes
  hooks : Hooks types
  recovery : RecoveryPolicy
  pointerEquality : Ptr types.Tag → Ptr types.Tag → EqualityChoice → Bool

inductive AllocationResult (Tag : Type) where
  | address (pointer : Ptr Tag)
  | unaddressable (provenance : Provenance Tag)
  | null

inductive Observation where
  | volatileRead (data : List UInt8)
  | volatileWrite (data : List UInt8)
  | io (operation : String) (channel : String) (data : List UInt8)

structure StepResult (T : LanguageTypes) (A : Type) where
  result : Except (Failure T) A
  store : Store T
  footprint : Footprint
  observations : List Observation

abbrev Operation (T : LanguageTypes) (Request Choice Result : Type) :=
  Store T → Request → Choice → Option (StepResult T Result)

structure MemoryOps (L : Language) (abi : ABI L.types) where
  allocate : Operation L.types (AllocRequest L.types)
    (PlacementChoice × AccessChoices L.types) (AllocationResult L.types.Tag)
  placeLiteral : Operation L.types (AllocRequest L.types × List UInt8)
    (LiteralChoice × L.types.HookChoice) (Ptr L.types.Tag)
  endLifetime : Operation L.types (AllocId × LifetimeEnd) L.types.HookChoice Unit
  free : Operation L.types (Ptr L.types.Tag) L.types.HookChoice Unit
  realloc : Operation L.types (Ptr L.types.Tag × AllocRequest L.types)
    (ReallocChoices L.types) (Ptr L.types.Tag)
  objectLifetime : Operation L.types (Region × L.types.ObjectLifetimeRequest)
    L.types.HookChoice Unit
  read : Operation L.types (Access L.types) (AccessChoices L.types) L.types.Value
  write : Operation L.types (Access L.types × L.types.Value) (AccessChoices L.types) Unit
  copy : Operation L.types (CopyRequest L.types) (AccessChoices L.types) Unit
  retag : Operation L.types (Access L.types × L.types.RetagRequest)
    L.types.HookChoice (Ptr L.types.Tag)
  encode : Operation L.types (L.types.CanonType × L.types.Value)
    ByteChoices (Array (Byte L.types.Tag))
  decode : Operation L.types (L.types.CanonType × Region)
    ByteChoices L.types.Value
  castPointer : Operation L.types (Ptr L.types.Tag × L.types.CanonType × L.types.CanonType)
    Unit (Ptr L.types.Tag)
  pointerToInt : Operation L.types (Ptr L.types.Tag × L.types.CanonType) Unit Int
  intToPointer : Operation L.types (Int × L.types.CanonType × L.types.CanonType)
    Unit (Ptr L.types.Tag)
  offset : Operation L.types (Ptr L.types.Tag × L.types.CanonType × Int)
    Unit (Ptr L.types.Tag)
  equal : Operation L.types (Ptr L.types.Tag × Ptr L.types.Tag) BoundaryChoice Bool
  compare : Operation L.types (OrderingTest × Ptr L.types.Tag × Ptr L.types.Tag)
    Unit Bool
  difference : Operation L.types (Ptr L.types.Tag × Ptr L.types.Tag × L.types.CanonType)
    Unit Int
  exposeOutput : Operation L.types (OutputExposure L.types.Tag) Unit Unit

end F2
```

Within a step, the core resolves relevant ranges, validates the choice and
does the byte or lifetime operation. The hooks receive the resolved ranges
and the original access tags. They update the relevant allocation and
location metadata and report the metadata locations they read or wrote.
The core checks the shape of these updates and joins their footprints to
the operation's own footprint. The core owns placement, exposure and byte
updates. A failed hook
reports metadata accesses through its failure and commits no hook updates.
`onAlloc` supplies initial metadata and a tag. `onDealloc` is called on
the old lifetime. `onCopy` receives the source snapshot and the current
destination store, in that order. `onObjectLifetime` handles object-lifetime
transitions inside live storage. `onRetag` returns the new tag alongside
any affected metadata. `encode` and `decode` use the same
representation rule as `write` and `read`. The evaluator invokes `decode`
on ranges resolved by an access. A `packedMember` request needs the member
layout evidence described below.

`typeLayout` returns byte size and byte alignment for an admitted complete
canonical type. The ABI also supplies scalar and pointer representations.
`encodeValue` and `decodeValue` use `Byte`, including its optional provenance
and pointer-fragment index. A pointer-containing aggregate therefore carries
the allocation tag through every member's encoded bytes. The fragment index
identifies the byte's position in that pointer representation and is preserved
by aggregate copies and `decodeValue`. It is not reconstructed from a value's
numeric address. Absent bytes in an encoded value mark positions whose values the transition chooses. The
profile defines which bit patterns trap and which layout or conversion
cases require a named refusal. An
allocation's `base` is absent for source objects without an address, such as
C objects declared `register`. Their direct lvalues still use the same store
and typed read and write rules. The `direct` designator is a language lvalue,
and is supplied only by an evaluator rule that designates that object.
A pointer consists of a concrete address and optional provenance. When
provenance is present, the offset is the signed difference from its
allocation's base. The address representation of null is supplied by the
ABI, with empty provenance. A non-null pointer may also have empty provenance.

Byte choices supply one value for each indeterminate read byte, unspecified
padding byte or partially written byte encountered by an operation, in its
specified range order. Values for partial bytes must agree with the bits
the operation preserves or writes. The transition checks the list against
the required choices. Choices for evaluation order and other external
inputs belong to the evaluator. Every run uses an admissible sequence of
choices and the correctness judgment covers all such runs. Footprints
identify the allocation, byte range and read, write or alias-metadata action. Operations with no
storage effects carry an empty footprint. Footprints are available to F3 for C17 §6.5p2 sequencing checks, including accesses
through aliases. Layout resolution and memory effects occur on the original
AST operation.

## Storage lifetime and resource exhaustion

A placement is chosen at the allocation step. Its alignment must suit the
request, its reserved interval must lie in the ABI's usable range, and it
must be disjoint from every live reserved interval. A valid one-past
address must fit the ABI address width. A placement's reserved interval
and its end address exclude zero and the ABI null address. A released
interval can be reused. A zero-size heap result has a distinct live token at a reserved
address with no accessible bytes. Its reservation has length one for
placement. The token can be compared, copied and passed to `free`. Its
accessible footprint is empty, including for PNVI-ae recovery. A function
has an ABI code placement and identity. An access to that identity uses
the applicable call or code-pointer rule.

Each `malloc` or `calloc` and each nonzero-size `realloc` may fail, even
when there is an admissible placement. Failure returns null and changes
the allocator effects promised by the library profile, such as `errno`.
The library evaluation rule performs those effects from the operation
result and includes their memory footprints. If the placement set is
empty, `fail` is the only admissible placement choice.
`calloc` checks the requested size product before allocation and initializes
the resulting bytes to zero on success. Static storage, addressable
literals, functions and vtables are placed during loading. Thread storage
is placed at thread startup. If a mandatory placement is impossible,
loading or thread startup fails without running that entry body. An
impossible mandatory automatic placement produces resource exhaustion
at the allocation step. For mandatory storage, `fail` is admissible
exactly when there is no placement. The execution profile maps this
failure to a load or automatic-exhaustion ending, according to storage
duration. An evaluated nonpositive VLA bound is UB independently of
resource exhaustion.

C automatic non-VLA objects start at entry to their block and end on exit
under §6.2.4p6. A VLA starts at its declaration and ends when execution
leaves its scope under §6.2.4p7. Plain GNU `alloca` and
`__builtin_alloca` keep storage until return from the calling function.
The GCC variants with a block-lifetime contract have their own lifetime
ending rule. Statement-expression locals end with the inner block. The GNU
temporary lifetime rule applies to a temporary created in the inner
statement that uses it. A C compound literal uses its declared scope
and storage duration under §6.5.2.5. The full-expression lifetime for
temporary objects under §6.2.4p8 is represented separately from the block
lifetime. Static and thread initialization uses the typed initialization
rule, including the ABI null encoding for pointer members. [GCC VLA], [GCC alloca], [GCC statement expressions]

`free(NULL)` succeeds without ending storage. Other arguments must be
the live heap allocation's returned base pointer. Interior pointers,
foreign storage and second frees are UB under §7.22.3.3. A successful
`realloc` snapshots the retained range and its metadata, ends the old
lifetime, validates placement in that state, and creates a fresh
allocation identity. The placement can reuse the old base. The retained
`min(oldSize, newSize)` bytes
are transferred with their provenance and corresponding effective-type
metadata. The added bytes are uninitialized. A failed `realloc` leaves
the old object live and its contents and metadata intact. `realloc(NULL,n)`
uses `malloc(n)`. For the GNU17/glibc instance, `realloc(p,0)` with
non-null `p` frees the block and returns null. This is the profile's C17
implementation-defined zero-size outcome. [DR 400], [glibc realloc]

A pointer with provenance from ended storage is indeterminate. Use of that
pointer value, including lvalue conversion to pointer type, comparison,
conversion, arithmetic or access, reports lifetime UB under §6.2.4p2.
Reusing its old address does not restore its provenance. A character access
to the representation of a separate live object still follows the byte
rules below.

The finite-address-space removal rule uses failure and placement separately.
An unused heap allocation and its matching free can be erased if success
versus failure cannot affect the remaining computation. Extend each run of
the erased program by taking the source allocation's always-admissible
null result and its `free(NULL)` step. Retain argument evaluations and
account for allocation-library effects such as `errno` when checking this
condition. Mandatory storage has no such null alternative. Removing or
merging its materialized space requires a source placement extension with
enough aligned capacity at every overlapping lifetime. Equivalently, a
compiler pass can supply a reservation proof for private shadow slots.
An erased allocation whose success, capacity use or resource-failure
outcome remains observable is outside that removal lemma. [Finite memory]

## Pointer representations and exposure

A pointer representation consists of the ABI bytes and their optional
provenance. A typed pointer write and its representation-preserving bulk
copy carry the original provenance. A pointer load of a null representation
yields the ABI null value. For a non-null load with a complete ordered pointer representation,
each byte must have its correct position in the ABI encoding and every
byte must carry the same optional provenance. Such a load retains that
optional provenance. Compatibility of the source and destination representation
classes is an ABI fact. Reading a pointer this way leaves exposure
unchanged. A typed load with the retained provenance of ended storage reports lifetime
UB. A non-character load of a trap for the accessed type reports
representation UB under C17 §6.2.6.1p5. [N2364], [TS 6010]

The shared `Byte` carries neither a representation class nor a byte
position. C's allocation metadata records contiguous intervals established
by typed pointer writes and representation-preserving copies. Each interval
describes its translation to positions in the source pointer encoding. This
supplies N2364's ordered-representation test even when a bulk copy splits a
range. An ordinary byte store invalidates the overwritten part of the
interval. A raw copy transfers the corresponding intervals from the source
snapshot. Equal numeric bits or equal provenance alone do not establish
that the positions remained in order. If the ordered-representation test
fails, decode the address and use the same exposed-allocation recovery as
integer-to-pointer conversion. This applies to pointer representations
synthesized in memory by ordinary character stores. [N2364]

The provenance of every live pointer representation inspected at a
non-pointer type becomes exposed. Aggregate decoding applies this rule to
each non-pointer scalar observation. A pointer-to-integer conversion and
pointer output with `%p` also expose the pointee's storage. Output of
provenance-carrying representation bytes, such as `fwrite`, exposes the
corresponding live storage. Pointer assignment, pointer loads through
compatible representations and opaque copying with `memcpy`,
`memmove` or `realloc` carry provenance without exposure. A manual
character copy exposes on its character reads. The ordinary integers it
computes carry no provenance. Exposure is a monotone update to the
allocation record for that lifetime. [N2362], [N2364], [TS 6010]

The cast to an integer uses the ABI representation of the actual pointer
address, including any object offset. The integer result has no provenance
token. The reverse cast uses the ABI address conversion first. An ABI null
address yields null. Otherwise, use the unique live exposed storage whose
byte footprint contains the address. Its base is included and its one-past address is
excluded. `recoveredTag` derives the C view from the live object, offset
and destination type. Where a required view is ambiguous, the operation
refuses as `recoveredSubobjectView`. With no matching allocation,
synthesize a non-null value with empty provenance. Before recovery, decline
`ambiguousOnePastAdjacentRecovery` when the address is both one past a live
exposed region and at the start of another live exposed region. PNVI-ae
synthesis at an isolated one-past address gives empty provenance. Strict provenance uses its language's explicit pointer-derived
operations to carry identity and does no exposed-allocation search.
Empty-provenance values retain their address for representation and
equality. An attempted access through one reports UB.
Pointer-to-pointer conversion and alignment are governed separately by
C17 §6.3.2.3p7. [N2364], [GCC pointers], [TS 6010]

## C lvalue access and bounds

C uses half-open subobject intervals for bounds. Pointer arithmetic and
subtraction must stay within the same array object, with a scalar treated
as an array of length one under §6.5.6p7–9. The stride is the element size.
The resulting pointer may be one past the last element, where access is UB.
Subtraction returns the element difference and requires representability in
`ptrdiff_t`. A pointer to a member narrows to that member or its array.
Conversion to a character pointer designates the bytes of the original
object under §6.3.2.3p7, including its padding. An ordinary conversion
preserves the designated object's bounds. A cast to a more strictly
aligned object pointer checks the concrete address against the target
alignment. Where recognized container recovery would need to widen a
member's view, the profile uses `enclosingObjectRecovery` until a rule
with the required object identity and layout evidence is admitted.
A C pointer's language tag carries the array or subobject view through
typed storage and representation-preserving copying. This is a C bounds
rule layered on PNVI-ae storage identity.

A flexible array member uses the largest array of whole elements that
fits the enclosing complete object under C17 §6.7.2.1p18, with the
parser's offset and the record layout's alignment and padding. An empty
replacement permits formation of the base but makes an access or a
pointer one past the hypothetical element UB. GNU zero- and one-length
trailing members use the documented extension along a terminal field path.
Regular fixed members retain their stated size for `sizeof`. GNU
extensions that would need a different enclosing layout are named
refusals until that layout is established. [GCC zero-length arrays]

Equality follows C17 §6.5.9p6. Two null pointers compare equal.
Pointers to the same object or function compare equal, including an object
and its initial subobject and pointers one past the same array. At a
comparison of one-past and another array's start, `adjacent` is admissible
exactly when the selected placements make the arrays immediately follow one
another. `separate` is admissible for nonadjacent placements.

When two live pointers have equal addresses but different provenance, or one
has empty provenance, the result is a language choice between true and false.
The choice is supplied by `Language.pointerEquality` and quantified under
rule 4. It is never inferred from the exposed flag. This includes equality
across every pair of provenances, including one-past values. The GNU17
instance may choose false at adjacent placements, matching the permitted GCC
and Clang result, while another admissible language choice may choose true.
An isolated one-past integer-to-pointer recovery remains a loud refusal when
the resulting value is used. [N2364 §3.3]
Ordered comparisons use §6.5.8p5. Admit the same array and its one-past
case, struct member declaration order, equal addresses for members of
the same union, and UB for unrelated objects. [N2364], [GCC PR 61502]

For C17 §6.5p6, declared type is permanent for an object that has one.
Every non-character store to an object without declared type establishes
the lvalue type for that store and later accesses that do not modify the
value. A character store changes the representation without retyping the
storage. `memcpy`, `memmove` and an established array-of-character copy
into storage without a declared type give the destination the source
effective type, if any. The copy snapshots source bytes, provenance and
effective-type metadata before any destination update. The effective-type
effect of an explicit character-array copy requires evidence of the
corresponding source and destination object ranges. The `characterArrayCopy` case of `copy` transfers only effective-type
metadata for an already established copy. Its individual character
expressions keep their own exposure, byte writes and sequencing semantics.
For other accesses to objects without declared type, §6.5p6 uses the
lvalue's type for that access. The C hook tracks typed ranges and their
subobjects through the location metadata. A case whose effective object
boundaries are unavailable is refused as `effectiveTypeBoundary`.

C17 §6.5p7 permits a stored value to be accessed through one of these
canonical lvalue types:

- A type compatible with the effective type under §6.2.7.
- A qualified version of a type compatible with the effective type.
- The signed or unsigned type corresponding to the effective type.
- The signed or unsigned type corresponding to a qualified version of the effective type.
- An aggregate or union type that contains a type from one of the first four bullets among its members, recursively through contained aggregates and unions.
- A character type.

Other accesses violate §6.5p7. The GNU `may_alias` attribute adds its
documented alias exception to this check. The requested type still
determines width, alignment and representation. C union reads reinterpret
the stored bytes as the selected member under §6.5.2.3p3 and its footnote.
The common-initial-sequence rule of §6.5.2.3p6 applies at its stated
visibility and compatibility conditions. C has no active-member guard.
A reinterpreted trap representation read at non-character type is UB.
Overlapping `memcpy` is UB under §7.24.2.1p2. `memmove` takes the same
byte and metadata snapshot and permits overlap under §7.24.2.2. [GCC attributes]

## Padding, initialization and volatile accesses

Initialized integer bytes decode according to the ABI, including integer
representations assembled by byte stores. A write to a structure or
union can give padding bytes unspecified values under §6.2.6.1p6–7.
A union store can also assign unspecified values to bytes for other
members outside the written member. These values are choices on that
store. Bit-field writes use Clang's storage-unit layout. Each updated byte
contains the new field bits and the previous value of the other initialized
bits. Where a byte was uninitialized, choose admissible values for its
untouched bits and store the resulting byte. A byte write that changes
only part of an existing pointer encoding invalidates the affected
representation lineage.

Read of an uninitialized automatic object is UB where the register rule
of §6.3.2.1p2 applies. Otherwise an unsigned-character read of an
uninitialized representation yields an unspecified byte on each read.
The choice leaves the storage uninitialized and is quantified independently
at each read. This includes permitted representation access through a
character lvalue even when the corresponding non-character representation
could trap. For other uninitialized typed reads in the admitted profile
use the named refusal `indeterminateTypedRead` when neither the register
rule nor a demonstrated trap applies. A demonstrated trap read through
a non-character lvalue is UB under §6.2.6.1p5. [DR 451]

String literal arrays have static storage duration. `placeLiteral` chooses
separate storage or reuse of a compatible read-only slice whose bytes and
alignment agree, including sharing identical suffixes when admitted by
the profile. A write to a literal is UB under §6.4.5p7. Volatile reads and
writes of represented objects emit ordered data observations as required
by §5.1.2.3p6. Direct volatile access through a fixed MMIO address outside
the represented environment has the named refusal `externalMMIO`.

## Observations, address independence and machine refinement

The observable projection contains ordered volatile access data, external
I/O operations and data at the system boundary, termination status, and
divergence. Observation records have no address or allocation ID fields.
When a program prints an address, the emitted characters are ordinary
I/O payload. Allocation, release, exposure, library copying and other internal
library actions contribute footprints for evaluation and proof. They
produce no extra observable event. A behavior may have infinitely many observations. In a finite observation
sequence, `events` returns `none` after its last event. UB and named
refusal are separate outcomes carrying the completed observable prefix.

```lean
namespace F2

inductive Ending where
  | exit (status : Int)
  | signal (number : Nat)
  | loadFailure
  | automaticExhaustion
  | diverges

structure Behavior where
  events : Nat → Option Observation
  ending : Ending

inductive RunOutcome where
  | defined (behavior : Behavior)
  | ub (observed : List Observation) (fault : String)
  | unsupported (observed : List Observation) (name : String)
  | exhausted (observed : List Observation) (kind : String)

structure MemoryStepAgreement (T : LanguageTypes) (Request Choice Result : Type) where
  stores : AllocId → Store T → Store T → Prop
  requests : AllocId → Request → Request → Prop
  choices : AllocId → Choice → Choice → Prop
  exceptions : AllocId → Store T → Store T → Request → Request → Prop
  results : AllocId → StepResult T Result → StepResult T Result → Prop

def operationRenames {T : LanguageTypes} {Q C A : Type}
    (op : Operation T Q C A) (r : MemoryStepAgreement T Q C A) : Prop :=
  ∀ id s₁ s₂ q₁ q₂ c₁ c₂ a₁,
    r.stores id s₁ s₂ → r.requests id q₁ q₂ → r.choices id c₁ c₂ →
    r.exceptions id s₁ s₂ q₁ q₂ → op s₁ q₁ c₁ = some a₁ →
    ∃ a₂, op s₂ q₂ c₂ = some a₂ ∧ r.results id a₁ a₂ ∧
      a₁.observations = a₂.observations

structure Executions where
  Program : Type
  World : Type
  Input : Type
  OtherChoices : Type
  Placements : Type
  Run : Type
  realizes : Program → World → Input → OtherChoices → Placements → Run → Prop
  outcome : Run → RunOutcome

structure PlacementAgreement (E : Executions) where
  initialObjects : E.World → E.World → Prop
  otherChoices : E.OtherChoices → E.OtherChoices → Prop
  exposed : E.Run → E.Run → Prop
  boundaryEquality : E.Run → E.Run → Prop
  castAlignment : E.Run → E.Run → Prop
  observedRepresentation : E.Run → E.Run → Prop

def outcomeSet (E : Executions) (p : E.Program) (w : E.World)
    (input : E.Input) : Set RunOutcome :=
  { outcome |
    ∃ choices placements run,
      E.realizes p w input choices placements run ∧
      E.outcome run = outcome }

def worldAgrees (E : Executions) (a : PlacementAgreement E)
    (w₁ w₂ : E.World) : Prop := a.initialObjects w₁ w₂

def choicesAgree (E : Executions) (a : PlacementAgreement E)
    (c₁ c₂ : E.OtherChoices) : Prop := a.otherChoices c₁ c₂

def matchesTarget (source : RunOutcome) (target : Behavior) : Prop :=
  match source with
  | .defined behavior => behavior = target
  | .ub observed _ => ∀ i event, observed[i]? = some event → target.events i = some event
  | .unsupported _ _ => False
  | .exhausted observed _ =>
      ∀ i event, observed[i]? = some event → target.events i = some event

An exhausted source run constrains a target only through its observed prefix.
The target may itself exhaust after any prefix that satisfies this relation.
This is the rule used when a removed allocation changes only whether a later
allocation can be placed. The source prefix remains a valid target behavior
up to the exhaustion point, and no suffix after that point is compared.

def runsAgree (E : Executions) (a : PlacementAgreement E)
    (r₁ r₂ : E.Run) : Prop :=
  a.exposed r₁ r₂ ∧ a.boundaryEquality r₁ r₂ ∧
    a.castAlignment r₁ r₂ ∧ a.observedRepresentation r₁ r₂

def runAddressIndependent (E : Executions) (a : PlacementAgreement E) : Prop :=
  ∀ p w₁ w₂ input choices₁ choices₂ placements₁ placements₂ r₁,
    worldAgrees E a w₁ w₂ → choicesAgree E a choices₁ choices₂ →
    E.realizes p w₁ input choices₁ placements₁ r₁ →
    ∃ r₂, E.realizes p w₂ input choices₂ placements₂ r₂ ∧
      runsAgree E a r₁ r₂ ∧
      matchesTarget (E.outcome r₁) (match E.outcome r₂ with
        | .defined behavior => behavior
        | .ub observed _ => { events := fun i => observed[i]?, ending := .diverges }
        | .unsupported observed _ => { events := fun i => observed[i]?, ending := .diverges }
        | .exhausted observed _ => { events := fun i => observed[i]?, ending := .automaticExhaustion })

def addressIndependent (E : Executions) (a : PlacementAgreement E) : Prop :=
  runAddressIndependent E a →
    ∀ p w₁ w₂ input,
      worldAgrees E a w₁ w₂ →
      outcomeSet E p w₁ input = outcomeSet E p w₂ input

def allocationRemoval (E : Executions)
    (erasable : E.Program → E.Program → E.World → E.World → Prop) : Prop :=
  ∀ source trimmed w₁ w₂ input c₂ ρ₂ r₂ behavior,
    erasable source trimmed w₁ w₂ →
    E.realizes trimmed w₂ input c₂ ρ₂ r₂ → E.outcome r₂ = .defined behavior →
    ∃ c₁ ρ₁ r₁, E.realizes source w₁ input c₁ ρ₁ r₁ ∧
      E.outcome r₁ = .defined behavior

The removal proof also has an exhaustion branch. If the source run reaches
finite-address exhaustion, `matchesTarget` compares only its completed
observable prefix. If the trimmed target run reaches exhaustion after a
source prefix, that target ending is permitted by the same prefix relation.
When a removed `malloc` has a null test folded to true, the source simulation
chooses its always-admissible null result and continues through `free(NULL)`.
The removal premise fails when allocation success, capacity, `errno`, or a
later use can distinguish that result.

abbrev FlatMemory (XLEN : Nat) := BitVec XLEN → UInt8

structure FlatMachine (Input : Type) (XLEN : Nat) where
  Program : Type
  Initial : Type
  Run : Type
  memory : Initial → FlatMemory XLEN
  realizes : Program → Initial → Input → Run → Prop
  observe : Run → Behavior

def flatRefinement {XLEN : Nat} (E : Executions) (M : FlatMachine E.Input XLEN)
    (initialMatches : E.World → M.Initial → E.Input → Prop)
    (materialized : E.Run → M.Run → Prop)
    (p : E.Program) (compiled : M.Program) (w : E.World) (start : M.Initial) : Prop :=
  ∀ input targetRun, initialMatches w start input →
    M.realizes compiled start input targetRun →
    ∃ choices placements sourceRun,
      E.realizes p w input choices placements sourceRun ∧
      materialized sourceRun targetRun ∧
      matchesTarget (E.outcome sourceRun) (M.observe targetRun)

end F2
```

An instance of these signatures fixes the relations from the store invariant
and the operational rules. For the single-allocation step lemma, the store
relation keeps all IDs, lifetimes, exposure flags, base-relative offsets,
effective types, and alias state in correspondence. It translates the
chosen allocation's base and the addresses of values with its provenance.
Pointer encodings are rebuilt at their recorded positions from the translated
values. All other byte values are equal. The relation applies through
environments, aggregate values, memory, and pending evaluation contexts.
In particular, a change to a live allocation's base requires admissible
old and new placements. Uninitialized bytes remain uninitialized in both
stores. Request and choice agreement supplies corresponding addresses,
accesses, heap failure decisions, literal links, byte choices and hook
choices. A newly created allocation uses the matching pair of admissible
placement choices. Result agreement preserves the outcome classification,
the store relation, the allocation-relative footprints and any returned
value up to the same translation. Each operation must prove
`operationRenames` in both directions with these relations.

For whole runs, initial objects agree by that correspondence and the
inputs and other choices are coupled. Couple evaluation order, external
results, allocation success or failure, literal sharing, and unspecified
bytes at their semantic choice sites. The primary theorem is the per-run
`runAddressIndependent` relation. It is proved by two simulations, one for
each direction, and carries the complete store relation, the exposure
relation, and the ending or exhaustion prefix. The equality of `outcomeSet`
in `addressIndependent` is a corollary obtained by existentially forgetting
the coupled choices and placements.

Compare runs whose exposure steps and exposed allocations correspond and
whose concrete bases agree for those allocations. The comparison also
requires agreement at the following address-sensitive operations.

1. Equality of pointers with equal addresses across any provenances, including
   empty provenance and every one-past/adjacent pair, uses the same
   `Language.pointerEquality` choice. The relation does not inspect exposure
   to choose the result.
2. Pointer casts preserve the outcome of the target alignment test.
3. Non-pointer observations of pointer representations use the same
   concrete bytes. This covers integer and character reads and any I/O or volatile
   payload that serializes those bytes. A typed volatile pointer access
   uses the ordinary pointer load or store rule. Exposure depends on
   whether the boundary serializes its representation as output.

These conditions are on the named operations and their operands. The
proof derives trace equality from them, including the ending, exhaustion,
and any observed prefix before UB or refusal. Run correspondence is obtained
by lifting the per-operation relation through the evaluator, including its
infinite runs. The simulations require the same exhaustion premise for the
paired finite-address stores. A source run that exhausts constrains its
target only through the prefix in `matchesTarget`, and a target may exhaust
after a source prefix. A case in which the exception premises differ remains
a separate admissible behavior in the corresponding set. Source correctness
requires every admissible resolution.

For allocation removal, the premise is a program and world correspondence
that differs only in the erased storage steps, with the retained
evaluations and capacity conditions stated above. For a heap pair, prove
the remaining transition correspondence after the null branch, including
library effects and all retained use sites. For mandatory storage, prove
a placement extension over the live intervals of each trimmed run,
including their ABI alignment, exposed bases and address-sensitive
operations. These are local simulation obligations of the transformation.
The existential in `allocationRemoval` is the construction that those
obligations discharge.

For flat refinement, the initial correspondence fixes the input,
ABI and any materialized initial bytes, addresses and permissions. A
source allocation materialized by the target is related to the target
interval at its chosen source address for the periods when its bytes
are represented there. Initialized bytes map to their value and discard
provenance. An uninitialized byte is related to each concrete value
consistent with the operations that observe it. A placement and value
relation follows the source identity when the target reuses a stack
slot. For a source value the machine keeps in registers, prove the
typed value correspondence and reserve a private source interval if
the source object is addressable. Reuse of a target interval for
overlapping source lifetimes requires a proof that no access or alias
can distinguish the shared representation for the two objects. The
source still needs disjoint admissible placements for those live
allocations. Whenever the program observes an object's address,
the correspondence preserves that address and its observed
representation. Source storage that would exceed the finite ABI
capacity needs a separate source failure simulation.

For every machine run at the given XLEN, supply a source run from the
same inputs and an admissible sequence of placements and other choices.
A defined source run matches the complete target behavior. A source UB
run matches the observable prefix through its first UB step, and the
materialization relation is required through that prefix. The relation
allows the target suffix after this point. A source refusal discharges
no target obligation. The compiler theorem also establishes the
initial correspondence for every initial state in its stated domain.

## GNU17 memory decisions

The oracle profile records the Clang version, target triple, data layout,
flags and libc. Compiler attributes and builtins below have their documented
GNU or Clang meaning for that profile. Extensions with different contracts
require distinct frontend evidence.

| Decision | GNU17 rule and evidence |
| --- | --- |
| Cast between pointer and integer | C17 §6.3.2.3p5–6 and §7.20.1.4 permit ABI-specific conversions. Use the selected pointer and integer representations and the PNVI-ae exposure rule above. [GCC pointers], [N2364] |
| Pointer conversion alignment | C17 §6.3.2.3p7 tests the converted address for the referenced type. The Clang ABI supplies the required alignment. [Clang alignment] |
| Allocation, failure and zero size | C17 §7.22.3 applies. Heap failure is allowed at every request. The profile admits a freeable zero-size allocation token on success. With glibc, non-null `realloc(p,0)` frees and returns null. C23 §7.24.3.7p3 instead makes that request UB. [DR 400], [glibc realloc], [C23] |
| Effective type and GNU alias exception | C17 §6.5p6–7 uses canonical compatible types. The GNU `may_alias` attribute allows access for aliasing purposes as through a character type. The underlying lvalue type still controls the byte width, alignment and representation. [GCC attributes] |
| Union punning | C17 §6.5.2.3p3 and p6 apply to union member reads. The GNU alias exception for type punning through a union requires the access through the union type. [GCC aliasing] |
| Invalid representations and indeterminate values | Use the C17 trap representation rule at §6.2.6.1p5 and the uninitialized automatic-object rule at §6.3.2.1p2. The unsigned-character choice is specified above. C23 §6.2.6.1p5 and §3.23–24 use non-value and indeterminate representations. [DR 451], [C23] |
| `_BitInt` representations | Standard `_BitInt` is C23. A Clang extension node for it in GNU17 reaches `bitIntRepresentation` until the profile has its size, padding and conversion rules. [Clang language extensions], [C23] |
| Packed, aligned and mode attributes | Use the emitted target layout. An access naming a packed member can use its attested alignment. A converted pointer or an ordinary indirect access uses the referenced type's alignment. A mode attribute needs the corresponding canonical ABI type and layout. [GCC attributes], [Clang alignment] |
| Flexible, zero-length and one-length arrays | ISO flexible members follow §6.7.2.1p18. GNU trailing zero-length members may affect enclosing size through tail padding. GNU trailing one-length arrays have the documented extension and occupy at least one element in the record layout. The parser's layout and enclosing object rule above determine the accessible extent. [GCC zero-length arrays] |
| String literal placement | C17 §6.4.5p7 admits sharing where the required elements fit. The chosen sharing respects read-only storage, alignment and the profile's documented merge policy. [GCC merging] |
| `alloca` and VLA lifetime | GNU plain `alloca` lasts to function exit. Specialized builtins use their documented block contracts. A VLA begins at its declaration and ends with its scope. A nonpositive evaluated VLA bound is UB under §6.7.6.2p5. [GCC alloca], [GCC VLA] |
| Statement expressions and temporaries | Use the GNU statement-expression's scope and the documented timing for destruction of temporaries created during its statements. C17 §6.2.4p8 governs ISO full-expression temporaries. [GCC statement expressions] |
| Volatile access | C17 §5.1.2.3p6 and §6.7.3 govern volatile data observations. Select the profile definition of a volatile access, including the access width and the case of a scalar expression in void context. [GCC volatile] |

## Native placement replay

Compile the unchanged source with pinned Clang 21.1.8, the GNU17 profile
flags and the selected ABI. Record the complete version and target for
every run. Record loader symbols, function entry addresses and heap results at the library boundary. For automatic objects and literals
used by a replay row, use Clang instrumentation after parsing to report
the declaration-site identity, activation, address and lifetime at the
needed events. The instrumentation must preserve the ordinary run's
result and ordering. Compare paired uninstrumented and instrumented
executions and verify the ABI and event mapping before admitting a row.
Coverage has to include every placement and choice that can affect the
row's result. Unrecorded placement choices require an independence
argument on that row. An incomplete or invalid replay produces an oracle
failure report.

Pass the recorded placements, allocation outcomes, literal sharing and
observable choice data into the model. A replayed choice must pass the
ordinary admissibility checks. Compare the model result and observation
data against the native run, using the recorded address for any
address-bearing output. For UB rows, record either the sanitizer diagnostic
or the cited C clause and source operand against the same pinned compiler and
source. A clean native sanitizer run does not by itself qualify a row as
defined. The row must be repaired, declined by
a named rule, or counted as a divergence. A single native replay
validates a particular resolution. The source correctness theorem
covers every admissible one. S2 must contain the replay runs before
reporting an F2 oracle result.

## Shared store migration and gates

C supplies bounds, effective type and lifetime rules through the
language instance. C++ supplies object lifetimes within live storage,
subobjects, active unions, pointer interconvertibility, transparent
replacement and `std::launder`. Function and vtable addresses use the
same placement and provenance mechanism. Migrate C first and move the
C++ `ObjectModel` callers to the shared operations before removing its
store and stateless alias predicate. Rust can map `StorageLive` and
`StorageDead` to the same storage operations and use tags and
location state for retagging. Its [Slice 1 memory contract] uses strict
provenance. The Slice 1 oracle accepts rows that agree under both Miri
borrow models. A subsequent Stacked Borrows or Tree Borrows instance
can implement its own hook policy.

Migrate the C evaluator off fabricated `(o,o)` placements,
`Ptr.toObject o o`, integer-to-object ID reconstruction and
`exposedAddress`'s independent address arithmetic. Retire `ptrInt`, the typed pointer and function byte variants, and the
unused exposure hook. Replace the cast whitelist and whole-record bit-field
concretization with the representation and field rules. Static literals use a loading-time placement instead of
per-evaluation allocation. Replace effective-type lookups used for
destination type guesses with the lvalue and copy rules above. Keep
evaluation order at the original AST nodes. F3 uses the store footprints
to test conflicts between unsequenced operations. Define the eventual
proof surface over the evaluator's behavior relation and derive the
runner from that relation.

- **S1, structured types.** The three Clang plugins are mandatory.
  Ingestion requires structured types joined by node ID in the same
  invocation. Expressions and declarations carry canonical shared
  `QualType` evidence. The gate is C17 compatibility and Clang layout
  through this path, deletion of `CType`, spelling literals and
  type-string operations, and deletion of `intTyOf?`, `torScalarSize`,
  `sizeAlign`, `recordsOf`, `isPtrType`, `isPtrIntType` and
  `cAliasCompatible`. The checker counts any restored `CType` alias.
  The regenerated frozen survey must show ≥1,326 MATCH out of 2,214,
  zero DIVERGE and zero UB verdicts lacking sanitizer or cited-clause operand evidence.
- **S2, shared store.** Begin after S1 passes, in a new language-parametric
  module. Every exported operation needs a well-formedness preservation
  theorem with a checked axiom list limited to `propext`,
  `Classical.choice` and `Quot.sound`. The differential gate is at least
  25 rows with zero DIVERGE under native placement replay. Cover literal
  identity and writes, static and calloc null encoding, defined torn
  integers, pointer-byte and function-pointer-byte reads and copies,
  partial bit-field writes and uninitialized reads, union punning,
  effective-type retyping and character-store preservation, allocated
  struct members, overlap rules, pointer integer difference and recovery,
  one-past equality and ambiguous recovery, alignment, alloca and VLA
  lifetimes, stale pointer equality, and realloc failure, in-place
  success and move.
- **S3, exposure and refinement.** Instantiate the C exposure and
  effective-type rules and prove evaluator-level `address_independent`
  with the same axiom gate. The 24 effective-type and 27 pointer/integer
  refusal rows each finish with MATCH, a UB verdict with sanitizer or
  cited-clause operand evidence, or a
  named permanent refusal. Begin the proof surface after S3.

[N2362]: https://www.open-std.org/jtc1/sc22/wg14/www/docs/n2362.pdf
[N2364]: https://www.open-std.org/jtc1/sc22/wg14/www/docs/n2364.pdf
[TS 6010]: https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3231.pdf
[C23]: https://www.open-std.org/jtc1/sc22/wg14/www/docs/n3220.pdf
[DR 260]: https://www.open-std.org/jtc1/sc22/wg14/www/docs/dr_260.htm
[DR 400]: https://www.open-std.org/jtc1/sc22/wg14/www/docs/dr_400.htm
[DR 451]: https://www.open-std.org/jtc1/sc22/wg14/www/docs/dr_451.htm
[glibc realloc]: https://sourceware.org/glibc/manual/latest/html_node/Changing-Block-Size.html
[GCC pointers]: https://gcc.gnu.org/onlinedocs/gcc/Arrays-and-pointers-implementation.html
[GCC attributes]: https://gcc.gnu.org/onlinedocs/gcc/Common-Type-Attributes.html
[GCC aliasing]: https://gcc.gnu.org/onlinedocs/gcc/Optimize-Options.html#index-fstrict-aliasing
[GCC PR 61502]: https://gcc.gnu.org/bugzilla/show_bug.cgi?id=61502
[GCC zero-length arrays]: https://gcc.gnu.org/onlinedocs/gcc/Zero-Length.html
[GCC alloca]: https://gcc.gnu.org/onlinedocs/gcc/Stack-Allocation.html
[GCC VLA]: https://gcc.gnu.org/onlinedocs/gcc/Variable-Length.html
[GCC statement expressions]: https://gcc.gnu.org/onlinedocs/gcc/Statement-Exprs.html
[GCC merging]: https://gcc.gnu.org/onlinedocs/gcc/Optimize-Options.html#index-fmerge-constants
[GCC volatile]: https://gcc.gnu.org/onlinedocs/gcc/Volatiles.html
[Clang alignment]: https://clang.llvm.org/docs/AttributeReference.html#align-value
[Clang language extensions]: https://clang.llvm.org/docs/LanguageExtensions.html
[Finite memory]: https://doi.org/10.1145/2737924.2738005
[Slice 1 memory contract]: rust-design.md#memory-interface
