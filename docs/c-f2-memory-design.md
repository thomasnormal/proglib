# C and Rust object-memory design

F2 supplies one object-memory interface for the C and Rust lanes. The
frontends provide declaration identity and layout facts. The memory core does
not parse type spellings or reconstruct an ABI. C23 clauses below refer to the
N3220 mirror used by this lane.

## Pointer interface

A pointer is a pair `(provenance, address)`. Provenance identifies the
allocation and its subobject lineage. Address is a concrete byte address. The
null pointer has no allocation provenance. An allocation chooses an address
from the set of aligned placements that do not overlap live allocations. That
choice is open in the semantics. A theorem quantifies over every permitted
placement, and pointer equality, ordering, subtraction, dereference, and
integer conversion observe only the choices allowed by C23 §6.3.2.3 and the
PNVI-ae-udi model. Deallocation invalidates the provenance while leaving any
old address unusable.

The front end supplies object size, alignment, subobject offsets, array
extent, and bit-field information as data keyed by declaration identity.
`resolve` checks provenance, lifetime, bounds, and alignment before an access.
No fallback derives a size or offset from a `CType` spelling. Rust's MIR
front end supplies the same facts for its allocations.

Pointer-to-integer conversion exposes an address according to PNVI-ae-udi.
The reverse conversion can recover a pointer only under that model's exposure
conditions. The result preserves the allocation provenance when recovery is
permitted. A C proof that does not cast or compare addresses can quantify over
the placement choice without mentioning an address.

## Abstract bytes

An object stores a sequence of abstract bytes. A byte is one of the following
forms.

* `indeterminate` records storage that has not received a value.
* `integer` records an integer representation fragment with its width and
  byte position.
* `pointer` records a pointer-representation fragment with its provenance and
  byte position.
* `character` records an ordinary character byte.

The representation is per byte, so a partially initialized object can be
copied with `memcpy` while a later typed read still checks every participating
byte. Typed loads and stores are defined by the language value-representation
rules in C23 §6.2.6.1 and the Rust representation supplied by its front end.
An indeterminate or torn non-character representation produces a named
outcome. It never becomes an arbitrary integer or pointer. The core exposes a
refinement relation to a flat byte memory for consumers that need concrete
addresses. The refinement preserves provenance and all observable bytes.

## Address independence

The central abstraction theorem has the following shape. Let `ρ₁` and `ρ₂` be
two admissible placement resolutions for the same initial objects and external
inputs. If a program does not expose an address through an integer cast,
address comparison, formatted output, or another address-observing external,
then its event trace and terminal outcome are equal under `ρ₁` and `ρ₂`, up to
the corresponding pointer values' addresses. Pointer provenance, object
identity, byte contents, lifetime faults, and aliasing decisions are
preserved. Ordinary correctness theorems can therefore state their result
without fixing concrete addresses. Programs that observe an address retain a
universal theorem over every placement choice.

## Aliasing parameter

The memory core takes an `AliasingModel` parameter with operations for a typed
access, a byte access, and a copy. The core itself handles provenance,
lifetime, bounds, alignment, and byte representation. C instantiates the
parameter with effective-type checks from C23 §6.5.1p6-p7. The check permits
compatible types and the standard's signed, unsigned, aggregate, and
character exceptions, and returns a named `effectiveType` fault otherwise.
Rust instantiates the same parameter with its borrow and aliasing model. A
Rust borrow violation is then a parameter outcome rather than a second object
store. Byte copies and character accesses remain shared operations.

## Requirements for ls-rust

The Rust lane needs allocation and deallocation events, provenance-preserving
pointer arithmetic, parser-native layout facts from rustc MIR, abstract-byte
copies, and the address-independence theorem. It also needs the aliasing
parameter to express mutable and shared borrows, stacked or tree borrows when
that model is selected, and the lifetime transitions attached to MIR storage
live and storage dead statements. Rust-specific rules must be supplied as
parameter cases over this interface. They must not fork pointer identity,
placement choice, or byte representation.

`docs/rust-design.md` is not present on the current master, so this page uses
the owner's confirmed F2 decision and the requirements in the lane inbox as
the Rust integration contract. The Rust-specific request can refine the
aliasing parameter after that document lands without changing the pointer or
byte interface.
