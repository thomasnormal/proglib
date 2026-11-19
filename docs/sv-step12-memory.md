# Step 12: one-rank unpacked storage in E

This note is the handoff for the one-rank unpacked-array shape used by a
parameterized register file such as `logic [W-1:0] cpuregs [P]`.  It describes
the canonical E route; it does not introduce a cycle model or a second store.

## Admission and representation

Slang's `UnpackedDecl` is retained as a source declaration.  At a concrete
parameter point, `PDecl.memShape?` evaluates the packed element width and the
unpacked bounds, and `MemShape` keeps the declaration name, element width and
source labels.  `MemState.ofShapes` creates one native memory object per
declaration.  It does not make one scalar declaration per cell and does not
unroll a parameterized bound.  Nested ranks, zero-width elements and shapes
that cannot be evaluated are loud refusals at `MemElab`.

The complete canonical state is `CoreMemState`, with the existing scalar
`Store` and one `MemState`.  `CoreMemDesign.initial` initializes both from the
same source-shaped declarations.  Scalar views are only a name-facing view
used while evaluating a body; `storeFromView` compacts that view back into the
authoritative scalar store at process boundaries.  There is no scalar-memory
coercion and no parallel `MemE` meaning.

## Reads and writes

An `ArraySel`/`PLhs.arrayElem` with exactly one index is evaluated at run time.
The index is converted to an `Int` and passed to `MemState.readIndexId` or
`MemState.writeTarget`; the source declaration supplies the label range.  A
known in-range index reads or writes that cell.  A known out-of-range read is
the all-x element required by IEEE 1800-2023 §§7.4.5 and 7.4.6, and an
out-of-range write has no effect (§11.5.1).  An x or z index is not guessed or
collapsed to a simulator choice: the native memory operation returns the
four-state result prescribed by the E memory boundary.  Partial array
targets, nested ranks and non-cell memory expressions refuse by name.

The index remains symbolic in the source AST and is evaluated when the
assignment executes.  Thus a `for (int i = 1; i < P; i++)` body is retained as
`PStmt.forLoop`; its runtime trip values issue one cell operation per
iteration.  No parameter-sized loop is expanded at elaboration.

## NBA timing and scheduling

For an edge process, the right-hand side and index are evaluated from the
pre-edge `CoreMemState`.  Cell updates are placed in the existing
`MemState.issueNba` queue, then committed once in the NBA region.  A scalar
NBA uses the same source-shaped queue and scalar destination width; it is not
represented as a memory cell.  Continuous assignments and `always_comb`
settle after the commit through the ordinary E fixed-point pass.  The edge,
NBA and settle order is the canonical E schedule, so the route preserves
IEEE 1800-2023 §§4.6, 9.4 and 10.4 rather than selecting a convenient order.

## Unknown and out-of-range cases

The memory object starts with the declaration's exact four-state initial value.
Known writes replace one cell; other cells are preserved.  An unknown index,
an out-of-range index and an uninitialized cell remain observable through the
same `LVec`/`Logic` operations as scalar E values.  The route never binds one
power-up unknown to a shared value or silently turns an x/z decision into a
Boolean branch.

## MemE status

The older `Kernel/MemE` and `MemCycle` files are compatibility and measurement
surfaces only.  New storage work belongs in `Kernel/MemElab.lean` and
`Kernel/CoreMemExec.lean`.  Any remaining MemE receipt must be justified by a
refinement theorem back to `CoreMemDesign.step`; it is not a second semantics
for users.  The `unpacked_cpuregs_e/canonical_agree.lean` receipt now runs the
source-shaped parameterized register-file envelope through
`CoreMemDesign.step` for all 11 x/z, write-enable, and NBA rows. Its simulator
checker reports 11/11 matching rows on Icarus Verilog 13.0 and Xcelium
24.03-s004. The next implementation gate is a full loaded design running
through the same dynamic-cell path at two parameter points.

## Current measured boundary — 2026-11-19

The source-shaped one-rank route is executable for the concrete clean-room
memory initializer at parameter points `(W, DEPTH) = (8, 2)` and `(32, 32)`.
The canonical probe initializes `mem[0]`, settles `q`, and preserves the
declaration width. Icarus Verilog 13.0 and Xcelium 24.03-s004 both report the
same `q=3c` value at the 8-bit point and the corresponding zero-extended value
at the 32-bit point. These rows exercise native `MemState` storage and the
time-zero continuous read without expanding cells or changing the source AST.

The DarkRISCV clean-room handoff reaches a successful canonical `initialState`
with one native memory and completes two reset-shaped passes. Its first
clocked transition reaches the source-shaped runtime `REGS[DPTR]` memory target
and does not return within the bounded execution window. This is a kernel-cost
wall, not a semantic refusal, so no whole-design E row or theorem is claimed.
The remaining Step 12 implementation work is the kernel-cheap edge/NBA path
for that dynamic cell target. The existing memory guards continue to cover
valid, x/z, negative, and out-of-range indices plus issue-order NBA commit.

## Time-zero settle receipt — 2026-11-19

The clocked route's `initialState` now performs the source-shaped continuous
assignment settle after declaration and initial-process effects. This follows
IEEE 1800-2017 §§4.5 and 10.3: a continuous assignment is an active-region
driver whose update must be visible at the first stable observation. The
change is recorded by `e245ebc5d` and is deliberately outside the clocked
step theorem until its settled-state premise is repaired.

The distinguishing clean-room row is
`sem2/initial_quiet_assign`. Before the change, the declaration view is
`y=x`; after it, canonical E returns `y=1`. Icarus Verilog 13.0 reports an
active-region value of `1` and settled rows `1,1`. Xcelium 24.03-s004 reports
an active-region value of `x` and the same settled rows `1,1`. The active
value is therefore not used as an oracle, while both simulators agree on the
post-`#0` and post-`#1` observations. The conservative claim is exact: an
admitted design whose continuous assignments leave its declaration-initialized
view unchanged has the same `initialState` result before and after the change.
Only designs whose first stable observation depends on a continuous driver can
change.

The declaration-width correction in `af38185ce` keeps an INT-class constant
initializer at the declared width under §§6.8 and 11.8. The source-shaped
`memory_unary_initializer` row therefore initializes a two-bit cell from
`value = -1` and settles `q=11`. Canonical E, Icarus Verilog 13.0, and
Xcelium 24.03-s004 agree on that row. Signal-dependent initializers still
refuse, so the correction cannot alter a previously admitted signal-driven
design. The related one-rank memory rows cover the same initializer at the
parameter points recorded above.

The runtime-initial-system-task guard in `b453d8ac4` follows IEEE 1800-2017
§6.3.1 and the open scheduling choice of §4.7. A branch whose condition reads
an unknown input cannot be assigned a simulator-specific truth value, so E
returns `Initial:runtime` before executing the task. The retained
`sem2/initial_syscall_e` receipt has source rows for `x`, `0`, and `1`.
Icarus Verilog 13.0 and Xcelium 24.03-s004 both accept the source and produce
the same `y=x` observations, while canonical E records the loud refusal. No
previously admitted E design contains a runtime initial system task, so this
guard is conservative over the admitted set.
