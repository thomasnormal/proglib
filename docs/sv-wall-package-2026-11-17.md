# SV wall package measurement — 2026-11-17

This note records the next ordered wall measurement after the asynchronous-reset
wall.  The asynchronous-reset row is parked: the current public real-design
census reports `present=0`, so there is no live refusal to remove.

The child-instance repro in the clean-room workspace was extracted
at the current public head and passed the ordinary collect-all census with zero
refusals.  The native-memory child repro
The clean-room child-instance memory fixture also passed with zero refusals.
These runs exercise the existing source-shaped hierarchy route; they do not
claim that the real-design table's four child-instance modules have moved.

The next ordered port-connection-target repro in the clean-room workspace
still reaches the
earlier typed-aggregate boundary first.  Its ordinary census reports
`VariableSymbol:type` for `state` and then
`Instantiation:E:unsupported: E memory route does not yet admit module member
'VariableSymbol:type'`; the extractor also retains `PortConnection:target` for
`out_state`.  The IEEE 1800-2023 §23.2.2 target cannot be admitted faithfully
until the typed struct declaration and member-path semantics are available.
This wall is therefore parked at its measured dependency, with no count
reduction claimed.

The census was run with the repository's `harness/sv/refusal_census.py`; gate
artifacts remain outside this repository.

The next process wall is the retained event-controlled procedural block
(`present=8` in the current table).  Its clean-room forms are
`event_control_repro.sv` and `event_generated_repro.sv`; the ordinary boundary
is the retained-process/event-list refusal.  Admitting it requires the
choice-bearing scheduler integration, which is explicitly prohibited before
the inbox records `ACCEPTED S1`, so this item remains a loud refusal and is
parked without a count claim.  The following initial-process wall is subject
to the same time-zero scheduler dependency.

The initial-process repro was measured separately. Canonical E's
`CoreMemDesign.initialState` executes the simple blocking assignment and the
ordinary census therefore reports zero E refusals. The `Design2`/`run2`
surface still emits `T2:Initial: initial process outside the cycle semantic
tier`; retaining that refusal is required until the time-zero state is part of
the scheduler-derived run2 semantics. The real-design initial-process count
is therefore unchanged.

The interface repro was remeasured from the current envelope.  Extractor rows
retain `InstanceSymbol:interface`, `InterfacePortSymbol:InterfacePort`, and
`PortConnection:InterfacePortSymbol`; the ordinary route reports those same
constructs and then `Instantiation:E:unsupported` at `PDesign.instantiateE2`.
The fixture also exposes hierarchical `bus.request` access and an assignment
target, so no interface semantics are inferred from the generic port route.
The real-design interface-instance, interface-port, and interface-port-
connection rows remain present=6 each.

Current-pin interface-instance receipt (2026-11-17): the clean-room checker
retains the exact `InstanceSymbol:interface`, `InterfacePortSymbol:InterfacePort`,
and `PortConnection:InterfacePortSymbol` boundaries. Xcelium 24.03-s004
matches four x/z rows; Icarus rejects the interface-port syntax, so no Icarus
oracle result is claimed. The real-design interface families remain present=6,
sole=0 each.

Current-pin interface-port marker receipt (2026-11-17): the same envelope
retains `InterfacePortSymbol:InterfacePort` in the interface declaration before
ordinary admission reaches the interface-instance boundary. This row is
predicted rather than a distinct ordinary refusal; the Xcelium four-row result
and Icarus parser boundary are recorded above, and no interface-port semantics
are claimed.

Current-pin interface-port-connection receipt (2026-11-17): the ordinary census
retains `PortConnection:InterfacePortSymbol / parsePConn / bus` before the
interface-instance E boundary. Xcelium 24.03-s004 matches four x/z rows;
Icarus rejects the interface-port syntax, so no Icarus oracle result is
claimed. The real-design connection family remains present=6, sole=0.

Stall-rule remeasurement: the public hierarchy corpus contains 90 envelopes;
the completed ordinary census has 63 refusal rows across 30 envelopes. The
remaining package walls occur once each for `PortConnection:target`,
`VariableSymbol:type`, `HierarchicalValueExpression`, and the interface
constructs; no public envelope emits the child-instance refusal. The largest
actionable ordinary family is outside this package (`Instantiation:E:unsupported`
19 rows, mostly parameter override context), followed by unrelated unsized-X/Z
rows (23 total). Ranking therefore keeps typed aggregate/member support ahead of
port-target admission, while child-instance admission has no public count to
flip. This remeasurement changes the next action from repeated wall receipts to
the typed aggregate dependency, pending an owner-assigned semantics item.

The delayed-event repro now gives a direct ordinary measurement:
`TimedStatement:DelayControl` at `parsePStmt` for `#1 q <= d;`.  This is a
time-control boundary under §9.4; it is retained as a loud refusal until the
scheduler models delay regions.  The real-design delay-control family remains
present=5, with no count reduction claimed.

For the final ordered clocks wall, the two-clock repro reports the exact
`Clock:multiple` loader refusal, while the derived-clock repro reports
`Clock:source` and the canonical-E `Event:time-zero` refusal.  The design note
in the journal treats both input clocks as free environment events, quantifies
over every interleaving including simultaneous edges, and leaves metastability
refused.  No source-order choice is introduced.  The real-design multiple
clock count remains present=4 and internal-clock count remains present=3 until
the scheduler is accepted.

The hierarchical-value repro was measured next. Both extractor and ordinary
collect-all retain `HierarchicalValueExpression` at `parsePExpr` for the
generic `u.internal_value` read. The existing hierarchy flattener handles
parser-native port connections, but it does not invent semantics for an
arbitrary hierarchical value expression (§23.6); the loud refusal remains
sound and the real-design present=7 count is unchanged.

Current-pin hierarchical-value receipt (2026-11-17): the wall checker reports
two rows matching Icarus Verilog 13.0 and Xcelium 24.03-s004. The ordinary
census retains `HierarchicalValueExpression / parsePExpr / u.internal_value`;
the real-design present=7, sole=0 count is unchanged and no arbitrary
hierarchical-value meaning is claimed.

The public-census handoff also confirms ownership boundaries: typed variable/member
paths, primitive instances, and specify blocks are `ls-sv3` rows in the current
wall table. Those measured rows are handed to that lane; this lane makes no
shared semantic change without an owner reassignment.

Pending-branch review at the current public master found no landable SV packet:
the parked `ls-sv3-w1-gate`, `ls-sv3-w1push`, and
`ls-sv3-parked-20261117-0438` branches delete or rewrite scheduler/core files
and large receipt suites in their diff to master. They were left untouched; no
branch with a clean, buildable wall-only delta is available for this lane to
land.

The public census also measured `inout_repro.sv` as the generic §6.6/
§23.2.2 inout wall (`PortSymbol:InOut` and `PortConnection:InOut`). The wall
table assigns both admission rows to `ls-sv3`; they are handed off without a
shared semantic change here.

Current-state audit at public master `82bb6353a` still shows the loader-owned
rows at child=4, event-controlled=8, initial=5, hierarchy value=7,
interface instance/port/connection=6 each, internal clock=3, multiple clocks=4,
and port target=6. The repository private-name self-test and diff check pass;
no newer owner instruction is present.

Current-pin discrepancy check: ordinary collect-all on both the checked-in
`Examples/system-verilog/sem2/child_instance_e/child_instance_e.sv.json` and
the clean-room `child_instance_scan.sv.json` returns zero refusals. This
conflicts with the older 03:37 handoff that names a child-instance refusal for
the latter shape. The older count is not treated as current evidence; a
current-pin remeasurement has been requested from the measuring lane.

Regenerating `child_instance_scan.sv.json` with the current Slang extractor and
rerunning ordinary collect-all also returns zero refusals. The discrepancy is
therefore not caused by a stale checked-in envelope; the older child-instance
handoff is stale relative to the current parser and route.

The current independent formal record also confirms the semantic landing: on
2026-11-16, canonical hierarchical E recursively merged
`scan_chain` → generated `scan_leaf` children, substituted genvar-indexed port
expressions, and matched Icarus/Xcelium (`q=0,0,0,1`). The remaining action is
only to remeasure the real-design table at the current pin; no present-count
transition is claimed here until that measurement lands.

The checked-in canonical receipt was also run directly at the current tree:
`lake env lean Examples/system-verilog/sem2/child_instance_e/agree.lean`
returned `Res.ok ["0", "0", "0", "1"]`. This independently confirms the
recorded Icarus/Xcelium child-hierarchy result; the real-design table still
needs its own count refresh.

Current-pin child-instance wall receipt (2026-11-17): the canonical-E hierarchy
checker reports four rows matching Icarus Verilog 13.0 and Xcelium 24.03-s004,
and its ordinary census has zero refusals. The intentionally unresolved-child
fixture remains a loud parser/admission boundary with
`UninstantiatedDefSymbol:UninstantiatedDef`, `SlangError:UnknownModule`, and
the enclosing `Instantiation:E:unsupported`; no simulator result is claimed
for that source. The real-design present=4 count is unchanged pending direct
source-overlay remeasurement.

The older generated-child wrong-answer audit is closed by the same hierarchy
landing. `generate_unbound_parameter_canonical_e/check.py` now reports eight
rows matching E, Icarus Verilog 13.0, and Xcelium 24.03-s004; the expected
connected-child sequence is `1,1,1,1,z,1,0,1`.

The internal-clock and internally driven-reset refusals were also rerun as
soundness receipts. `clk_internal/check.py` and `clk_rst_int/check.py` each
report 10 x/z rows matching Icarus Verilog 13.0 and Xcelium 24.03-s004; the
ordinary loader refuses `Clock:source`/`Clock:reset`, and canonical E refuses
the corresponding event-source boundary. No internal-clock or reset meaning is
silently approximated.

Current-pin asynchronous-reset cleared-wall receipt (2026-11-17): active-low
and active-high canonical-E/loader checks each report 19 source rows matching
Icarus Verilog 13.0 and Xcelium 24.03-s004, including x/z reset and clock-edge
cases. Both supported forms are ordinary-admitted; the real-design family is
present=0, sole=0. Generated/internal resets remain separate refusals.

Ordered wall-package status at public master `f595abb64` (2026-11-17): the
recovered asynchronous-reset handoff and every subsequent ordered handoff
(child instance, port target, delay, event process, hierarchy value, initial,
interface instance/port/connection, internal clock, and multiple clocks) have a
current receipt in this document. No active wall handoff remains in the inbox;
the remaining real-design counts are unchanged until direct source-overlay
remeasurement, and a new owner instruction is required for the next item.

Current-pin internal-clock receipt (2026-11-17): the dedicated generated-clock
fixture reports five rows matching Icarus Verilog 13.0 and Xcelium 24.03-s004.
Its ordinary census retains `Clock:source` at `PDesign.clockReport` and the
canonical-E `Event:time-zero` boundary at `PDesign.instantiateE2`; no derived
clock meaning is claimed. The real-design internal-clock family remains
present=3, sole=0.

The scalar topological-chain receipt is also current: `backreg_e/check.py`
regenerates its envelope byte-identically, canonical E refuses the §10.3
topological boundary, and all eight x/z rows match Icarus Verilog 13.0 and
Xcelium 24.03-s004. The route makes no stale-value claim for this shape.

The two-clock receipt was refreshed after its source-shaped envelope was found
stale (old source hash and spans). Approved re-extraction now makes the
envelope byte-identical; `clk_two/check.py` reports ordinary run2
`Clock:multiple` refusal and eight x/z rows matching Icarus Verilog 13.0 and
Xcelium 24.03-s004.

Current-pin multiple-edge-clock receipt (2026-11-17):
`multi_clock_domain_e/check.py` reports eight rows matching Icarus Verilog
13.0 and Xcelium 24.03-s004, including separate, coincident, stopped, ratio,
and x/z clock cases. The ordinary run2 route retains exact `Clock:multiple`;
canonical E supplies the direct two-clock receipt. The real-design family
remains present=4, sole=0; no scheduler interleaving is selected.

The event-list refusal receipts are current as well: `event_control_wall` and
the implicit/signal event fixtures regenerate byte-identically, match all
Icarus Verilog 13.0 and Xcelium 24.03-s004 x/z rows, and retain the exact
`Clock:implicit` event-list refusal. No unsupported implicit sensitivity is
executed by E.

The level-sensitive `always_latch` receipt is current: its Lean canonical-E
agreement passes, and the six-row x/z fixture matches Icarus Verilog 13.0 and
Xcelium 24.03-s004. This confirms the admitted latch form's measured behavior;
hardware metastability and latch-enable glitches remain outside the model.

The canonical time-zero memory receipts are current: `memory_initial_canonical_e`
matches three rows on Icarus Verilog 13.0 and Xcelium 24.03-s004, and
`readmemh_rom_canonical_e` regenerates byte-identically with five rows matching
both simulators. These receipts cover known and x indices plus literal
`$readmemh` initialization without adding a run2 meaning.

The memory execution receipts remain green: `always_comb_memory_canonical_e`
and `always_comb_case_memory_canonical_e` each match four rows on Icarus
Verilog 13.0/Xcelium 24.03-s004, and `memory_edge_blocking_canonical_e`
matches three source rows on both simulators. These receipts cover time-zero
combination, memory NBA/read behavior, and blocking edge assignments.

The edge-case memory receipts are current: `memory_edge_case_canonical_e` and
`memory_edge_casez_casex_canonical_e` regenerate byte-identically and each match
six source rows on Icarus Verilog 13.0 and Xcelium 24.03-s004, covering plain
case, casez, and casex edge assignments.

The asynchronous-memory FIFO receipt is current: `async_mem_fifo_canonical_e`
regenerates byte-identically and its five canonical-E rows match Icarus Verilog
13.0 and Xcelium 24.03-s004.

The memory-order receipt is current: `mem_order_e/check.py` passes its MemE
boundary checks, and both Icarus Verilog 13.0 and Xcelium 24.03-s004 match two
rows each for `mem_order_e` and `mem_always_comb_e`.

Packed-shift receipts are current: `packed_shift_canonical_e` and
`packed_shift_mem_e` each match eight rows on Icarus Verilog 13.0 and Xcelium
24.03-s004; `packed_shift_register_canonical_e` regenerates byte-identically
and matches 18 rows across N=4/N=8, including first, x, and z clock/data cases.

The net/metadata receipts are current: `memory_metadata_canonical_e` matches
two rows on both simulators, `net_z_output_port_canonical_e` matches two
undriven-output rows, and `net_z_scalar_canonical_e` matches two undriven-net
rows including a bit select.

The generated/parameterized memory receipts are current: `generate_memory_canonical_e`
regenerates byte-identically and matches eight rows on both simulators;
`param_mem_child_e`, `param_mem_input_gen_e`, and `param_mem_shift_e` each
match ten rows on Icarus Verilog 13.0 and Xcelium 24.03-s004.

The parameterized memory-shape receipts are current: shape A matches 12 rows,
shape B one hierarchy-memory row, shape C four generated-array rows, and shape
D six loop-local/x-index rows on Icarus Verilog 13.0 and Xcelium 24.03-s004.

The task-memory receipt is current: `task_memory_e/check.py` passes its
empty-task and source-shaped memory guards, with three rows matching Icarus
Verilog 13.0 and Xcelium 24.03-s004.

The scalar nonblocking memory receipt is current: `memory_scalar_nba_e/check.py`
reports five rows matching canonical E, Icarus Verilog 13.0, and Xcelium
24.03-s004. This covers the scalar memory NBA shape without admitting a
different scheduling meaning.

The wildcard time-zero receipt is current: `always_star_timezero_e/check.py`
reports four startup rows matching the canonical source behavior on Icarus
Verilog 13.0 and Xcelium 24.03-s004. The startup ordering split is retained
as measured simulator behavior; no unmodelled time-zero event is approximated.

The wildcard memory-read receipt is current: `always_star_memory_read_e/check.py`
reports nine rows matching the source-shaped canonical behavior on Icarus
Verilog 13.0 and Xcelium 24.03-s004.

The implicit-event memory receipt is current: `memory_implicit_event_canonical_e/check.py`
reports three canonical-E rows matching Icarus Verilog 13.0 and Xcelium
24.03-s004.

The wildcard-case memory receipt is current:
`always_comb_wildcard_case_memory_canonical_e/check.py` regenerates its
envelope byte-identically and reports four rows matching canonical E, Icarus
Verilog 13.0, and Xcelium 24.03-s004.

The implicit-event latch-case receipt is current:
`always_star_case_latch_e/check.py` passes its retention check and reports
eight rows matching the source behavior on Icarus Verilog 13.0 and Xcelium
24.03-s004; the first startup row is the documented simulator split.

The implicit-case memory receipt is current:
`memory_implicit_case_canonical_e/check.py` reports four canonical-E rows
matching Icarus Verilog 13.0 and Xcelium 24.03-s004.

The fixed-array index receipt is current:
`array_index_canonical_e/check.py` regenerates its envelope byte-identically
and reports eight known/x/z rows matching canonical E, Icarus Verilog 13.0,
and Xcelium 24.03-s004.

The real-design census was refreshed after the parameterized whole-array copy
landing. On pinned OpenTitan `prim_arbiter_ppc`, the measured
`AssignmentExpression:target`/`GenItem.expand` residue moved from 1 to 0;
the generated real-design row therefore moves from 6 to 5 unsupported nodes,
while its first remaining wall stays `LocalDecl`.

Current-head status after the concurrent public Python pushes: public master is
`8c86906cd`, with no SV semantic change after `fc95337c5`. The real-design
flip above remains the current SV measurement; the E import-closure audit still
reports the pre-existing `Sem2`/`Sem2Run`/`Spec2` reach and is retained as a
red-before baseline in the lane gate log.

The hierarchy child-aggregate preservation landing `67f623196` is also current.
The canonical child and parameterized-hierarchy receipts regenerate and match
Icarus Verilog 13.0 and Xcelium 24.03-s004. The typed aggregate port-target
receipt still reports `PortConnection:target / parsePConn / hwif_out` after the
earlier `VariableSymbol:type` boundary, so no typed-aggregate meaning is
claimed. Its affected-module build passes; the broad dependent build reaches
878 targets and remains red only on pre-existing refusal expectation rows and
lead-owned SeqCycle/function proofs, with the first refusal lines captured in
the gate log.

Current-pin port-connection-target receipt (2026-11-17): the faithful structured
fixture reports `PortConnection:target / parsePConn / hwif_out`, then the
independent `VariableSymbol:type` and E boundaries. Xcelium 24.03-s004 matches
all four x/z rows; Icarus cannot elaborate the unpacked-struct source, so no
Icarus oracle result is claimed. The real-design present=6 count is unchanged.

The pinned CV32E40P v1.0.1 handoff reaches a retained `BreakStatement` inside
an edge-process loop at `rtl/riscv_hwloop_controller.sv:90` and
`rtl/riscv_fetch_fifo.sv:157`. This is routed to ls-sv2 as its generic
loop/process ingestion wall, with the minimal parameterized for/break repro
and both pinned simulator rows retained there; ls-sv makes no source rewrite or
semantic claim for it.

The prim_packer `ready_o` handoff is a separate §6.6 resolved-net wall: its
metadata reports two generated drivers, so the current E refusal is sound and
must not be relabelled as an undriven-net z case. A per-driver strength and
resolution relation remains an unassigned general-E item.

The public resolved-net controls were rerun for this handoff. The live
two-driver `assign_net_resolution.sv` control prints `y=x` on Icarus Verilog
13.0 and Xcelium 24.03-s004. The static literal-driver control is a simulator
startup split: Icarus prints `conflict=x, agree=1, z_only=z, unknown=x`, while
Xcelium prints `x,x,x,x` at time zero. No canonical-E agreement is claimed for
that split; both controls remain outside the E driver-set semantics.

At current public master `4f358ba16`, the wall-package semantic pin remains
`fc95337c5`; subsequent SV commits are refusal preservation, routing, and
measurement documentation only. The anonymous real-design head remains 25
modules total, 3 loading, and 3 running; no resolved-net count transition is
claimed from this simulator-split measurement.

The fresh Ibex exact-closure measurement is routed to ls-sv3 Param/enum
ownership: 224 sources, 20 modules, 587 static unsupported nodes, and first
wall `defaults: enum 'base_isa_e': unrecoverable packed dimensions` at
`rtl/ibex_pkg.sv:36-39`. No ls-sv extractor or semantic change is made.

The CV32E40P break repro is also fully measured: Icarus Verilog 13.0 and
Xcelium 24.03-s004 both print `x, x, 0, 0, 1` for the parameterized
for/break fixture, while the retained envelope reaches the named
`BreakStatement` refusal. The symbolic ingester now keeps that parser node as
a loud `PStmt.unsupported` statement, so the envelope itself loads and the
ordinary census reports `BreakStatement` at `parsePStmt`; no loop lowering or
E meaning is introduced here. The real-design first wall consequently moves
to the next retained generate-member boundary, with no claim that a real-design
count has dropped.

Current public master is `69530791d`; the private-name cleanup is on master and
the wall package remains clean under the required public-tree gate.

CURRENT HEAD CORRECTION — 2026-11-17T10:45Z

Public master is now `fdfbc6b06`; the intervening SV change records the
CV32E40P break-wall evidence only. The measured break rows remain
`x, x, 0, 0, 1` on both pinned simulators, and the retained envelope refusal
remains unchanged. No real-design count transition is claimed.

CURRENT HEAD CORRECTION — 2026-11-17T10:55Z

Public master is now `ef58c13a0`; the intervening SV change updates
wall-package head documentation only. The CV32E40P break evidence and refusal
boundary are unchanged, and no real-design count transition is claimed.

The delayed-control wall receipt is current: `delay_control_wall/check.py`
reports four rows matching Icarus Verilog 13.0 and Xcelium 24.03-s004, while
the ordinary census retains the exact `TimedStatement:DelayControl` refusal.
The zero-delay E route makes no timing approximation.

Current-pin delay-control receipt (2026-11-17): the clean-room ordinary census
retains `TimedStatement:DelayControl / parsePStmt / #1 q <= d;`; its four x/z
rows match Icarus Verilog 13.0 and Xcelium 24.03-s004. The real-design family
remains present=5, sole=0 and predicted because ordinary admission reaches the
retained event-process boundary first; no timing meaning is claimed.

The explicit event-control wall receipt is current:
`event_control_wall/check.py` reports four rows matching Icarus Verilog 13.0
and Xcelium 24.03-s004, while the ordinary census retains the exact
`Clock:implicit` event-list refusal. The source is not reinterpreted as
`always_comb` or latch semantics.

Current-pin event-controlled-process receipt (2026-11-17): the same four rows
match Icarus Verilog 13.0 and Xcelium 24.03-s004. The ordinary census retains
both `Clock:implicit` lines from `parsePProcess` and `PDesign.instantiateE2`
(`event-controlled process has no supported edge or implicit sensitivity
semantics`). The real-design event-controlled family remains present=8, sole=0;
no event-list scheduler meaning is claimed.

The initial-storage receipt is current: `initial_storage_e/check.py` reports
two rows matching Icarus Verilog 13.0 and Xcelium 24.03-s004. Canonical E's
`initialState` executes the simple blocking initialization, while the ordinary
run2 surface retains `T2:Initial: initial process outside the cycle semantic`
refusal until scheduler-derived time-zero semantics is available.

Current-pin initial-process receipt (2026-11-17): the canonical-E agreement
remains `.ok ["0", "0"]`, both pinned simulators match its two rows, and the
ordinary hierarchical census reports zero refusals for this admitted E shape.
The real-design initial-process family remains present=5, sole=0 because the
legacy Design2/run2 route still refuses ordinary runtime initial actions; no
new time-zero scheduler claim is made.

The canonical memory-initialization receipt is current:
`memory_initial_canonical_e/check.py` reports three rows (time-zero
initialization, known index, and x index) matching canonical E, Icarus Verilog
13.0, and Xcelium 24.03-s004.

The `$readmemh` ROM receipt is current:
`readmemh_rom_canonical_e/check.py` regenerates its envelope byte-identically
and reports five time-zero rows matching canonical E, Icarus Verilog 13.0, and
Xcelium 24.03-s004.

The edge-memory case receipt is current:
`memory_edge_case_canonical_e/check.py` regenerates its envelope
byte-identically; its two source-shaped canonical-E rows and six simulator
source rows match Icarus Verilog 13.0 and Xcelium 24.03-s004.

The wildcard edge-memory receipt is current:
`memory_edge_casez_casex_canonical_e/check.py` regenerates its envelope
byte-identically; its two source-shaped canonical-E rows and six simulator
source rows (case, casez, and casex) match Icarus Verilog 13.0 and Xcelium
24.03-s004.

CURRENT HEAD CORRECTION — 2026-11-17T11:05Z

Public master is now `1f8c98756`; the intervening public change is a
private-name cleanup outside SV semantics. The delayed-control receipt and its
`TimedStatement:DelayControl` refusal remain unchanged.

## Generate-for implicit event process wall

The pinned CV32E40P source contains a `GenerateFor` whose body is the parser's
`AlwaysEvent` with `event_kind: "ImplicitEventControl"` (the generated loop in
`riscv_hwloop_controller.sv`). `parseGenItem` now dispatches that parser node
through `parsePProcess`, preserving its `PProcess.alwaysImplicit` body. Explicit
event-list forms still take the existing loud refusal; no generated loop is
unrolled and no event is reinterpreted as a clocked process.

A clean-room parameterized generate-for fixture with one source-shaped
`always @*` writer passes the collect-all extractor and ordinary census after
this change. Icarus Verilog 13.0 and Xcelium 24.03-s004 agree on its known and
x/z rows: `00, 01, 10, 11, 00, 00, 00, 00`. The source-shaped process remains
subject to the existing scheduler and fixed-point boundaries in later routes.

## For-loop wall remeasurement

The current public clean-room `for_loop.sv` source was re-extracted with the
approved procedural-retention mode and passed through the ordinary census.
The extractor retains the finite loop body, the ordinary census reports zero
refusals, and canonical E produces eight source cycles matching Icarus Verilog
13.0 and Xcelium 24.03-s004 (`xxxxxxxx` at each sample because the four array
cells have no initializer). This is a measurement only: the generic
`ForLoopStatement` wall remains assigned to ls-sv3 in the current census, no
real-design count transition is claimed, and no loop lowering or new scheduler
meaning was added in this lane.

## Procedural local-iterator wall

The parameterized `proc_local_for_automatic.sv` clean-room source keeps a
block-local automatic `int` iterator in an `always_comb` procedural loop. The
canonical-E route retains the loop and returns the named refusal
`9.2.2.2: procedural loop in always_comb body is outside this slice` at both
N=4 and N=8. Icarus Verilog 13.0 and Xcelium 24.03-s004 agree on the source
rows at N=8 but diverge at N=4 on the inactive high bits. No simulator oracle
result is claimed for that divergent point, and the source remains outside the
receipt manifest. No loop lowering, E-row admission, or real-design count
transition is claimed.

## Nested unpacked-target wall

The parameterized `nested_unpacked_target.sv` clean-room source keeps a
two-rank unpacked `weights[row][col]` target in generated edge processes. The
ordinary census retains the parser's default-point index rows, then canonical
E refuses the declaration with
`decl 'weights': nested unpacked memory rank outside E (UnpackedDecl:rank)`.
Icarus Verilog 13.0 and Xcelium 24.03-s004 agree on all six source rows,
including reset, known, x, and z data. No nested-memory E execution or
real-design count transition is claimed.

## Parameterized packed-enum literal wall

The parameterized `packed_enum_dimension_repro.sv` clean-room source keeps the
unsized enum member literal `MODE_A = '0` inside a packed enum whose width is
set by `W`. Slang retains the parser-native
`EnumValueSymbol:unsized-literal-member` expression, and the ordinary route
refuses that expression before canonical E execution. Icarus Verilog 13.0 and
Xcelium 24.03-s004 agree on six source rows for `0`, `1`, `x`, and `z` values.
No parameterized enum E execution or real-design count transition is claimed.

## Memory-cell identifier wall remeasurement

The public clean-room `memory_cell_identifier.sv` fixture uses `cell` as a
signal identifier inside a generated block. Slang's approved parser retains
`EmptyMemberSymbol:EmptyMember` and syntax diagnostics at the declaration and
uses; the ordinary census reports those parser-native errors before the E
route. Icarus Verilog 13.0 rejects the source with syntax errors, while
Xcelium 24.03-s004 rejects elaboration (including the two generated continuous
drivers on `q`). No simulator value is claimed. The identifier is outside the
language grammar, so this wall needs no semantic admission or source rewrite;
the loud parser refusal remains the exact boundary.

## Reactive preemption wall remeasurement

The clean-room `preempt_block_refuse.sv` fixture has two `always_comb`
processes where the first writes `q` and the second reads it. Ordinary E
refuses it at `PDesign.instantiateE2` with
`Comb:dependency-order: 9.2.2.2/9.4.2.2: reactive process reads 'q' from
itself or a later reactive process; canonical E has no fixed-point scheduler`.
Icarus Verilog 13.0 and Xcelium 24.03-s004 agree on the five measured rows:
all-x, `a=0`, `a=1`, `a=x`, and `a=z` produce matching q/r/z values in each
case. The receipt claims no source-order or preemption resolution; the loud
fixed-point boundary remains sound.

## Array-index wall remeasurement

The ranked `array_index.sv` clean-room row is already admitted on the current
tree. Approved extraction and the ordinary census both report zero refusals,
and the canonical-E batch receipt matches Icarus Verilog 13.0 and Xcelium
24.03-s004 on all eight cycles (`xxxxxxxx` throughout because `values[0:3]`
has no initializer). This is a cleared/stale ranking row: no semantic change,
no array-index lowering, and no new real-design count transition is claimed.

## Generated-array nested-index wall remeasurement

The ranked `generated_array_nested.sv` row is already admitted with the
approved procedural-retention extraction. Its ordinary census reports zero
refusals. Canonical E matches Icarus Verilog 13.0 and Xcelium 24.03-s004 for
all eight cycles at both W4 and W8, including the x/z rows (`xxxxxxxz`), with
the measured values retained by the receipt. The prior topology-boundary
ranking is stale on this tree; no generated-index lowering, memory semantics
change, or real-design count transition is claimed.

## Default-point array wall remeasurement

The ranked `default_point_array.sv` row is already admitted with retained
procedural loops. Approved extraction and ordinary census report zero
refusals, and canonical E matches Icarus Verilog 13.0 and Xcelium 24.03-s004
for all eight cycles (`xxxxxxxx` throughout because the four pipe cells are
uninitialized). This ranking row is cleared on the current tree; no array
lowering, semantic change, or real-design count transition is claimed.

## Undeclared array-select wall remeasurement

The ranked `array_select.sv` fixture selects `missing[i]` without declaring
`missing`. Approved extraction emits `ContinuousAssignSymbol:InvalidExpression`
and `SlangError:UndeclaredIdentifier`; ordinary E preserves those parser-native
refusals and reports the same E instantiation boundary. Icarus Verilog 13.0
and Xcelium 24.03-s004 both reject elaboration, so no simulator value is
claimed. This is an invalid-source boundary, not an array-index semantic wall;
no source repair or semantic admission is appropriate.

## Undriven output-net wall remeasurement

The legal `wire_output_port.sv` fixture has an undriven four-state output wire
as specified by IEEE 1800-2023 §6.6. Approved extraction and the legacy
`PDesign.instantiate` census retain `PortSymbol:net-z`, but canonical E has no
`PDesign.instantiateE2` refusal. Icarus Verilog 13.0 and Xcelium 24.03-s004
agree on four rows: `y=zzzzzzzz` for known, x, and z input values. The
canonical-E wall is cleared on this shape; no net-resolution change is made.

## Signal-event-control wall remeasurement

The clean-room `signal_event_control.sv` fixture uses `always_ff @(clk)`
without an edge keyword. Approved extraction emits
`SignalEventControl:None_`; ordinary E emits `Clock:implicit` at both
`parsePProcess` and `PDesign.instantiateE2`, because no level-event scheduler
is modeled. Icarus Verilog 13.0 and Xcelium 24.03-s004 both accept the source
with the same missing-edge warning and produce identical eight sampled rows,
including x/z clock values. No E value is claimed; the level-event refusal
remains loud under IEEE 1800-2023 §9.4.2.

## Undeclared net wall remeasurement

The ranked `net_z.sv` fixture assigns `missing` to `y` without declaring
`missing`. Approved extraction emits `ContinuousAssignSymbol:InvalidExpression`
and `SlangError:UndeclaredIdentifier`; ordinary E preserves those diagnostics
and refuses at the E instantiation boundary. This is not a legal undriven-net
(`net-z`) case, so no simulator value or net-resolution semantics is claimed;
the parser-native refusal remains loud.

## Invalid continuous-assignment wall remeasurement

The ranked `invalid_continuous_assign.sv` fixture uses undeclared `missing` in
`{x, missing} >> 1`. Approved extraction emits
`ContinuousAssignSymbol:InvalidExpression` and `SlangError:UndeclaredIdentifier`;
ordinary E preserves those diagnostics and refuses at the E instantiation
boundary. This is invalid source rather than a width or continuous-assignment
semantic case, so no simulator value or semantic admission is claimed.

## Typed unpacked-net wall remeasurement

The ranked `typed_array.sv` fixture declares legal unpacked wire storage
`values [0:3]`. Approved extraction emits `NetSymbol:type`; ordinary E
preserves that member boundary and refuses at `PDesign.instantiateE2`. Icarus
Verilog 13.0 and Xcelium 24.03-s004 both compile the source and agree on four
rows (`y=xxxxxxxx` for known, x, and z inputs because the net cells are
undriven). No net-resolution approximation or semantic admission is claimed.

## Edge-child instance wall remeasurement

The ranked `edge_child_instance.sv` fixture is already admitted through the
canonical hierarchy merge. Approved extraction and ordinary census report no
refusal, and the existing canonical-E receipt passes two source rows on Icarus
Verilog 13.0 and Xcelium 24.03-s004 (`y=x`, then `y=0`). The child edge body
and connected ports remain source-shaped; no hierarchy lowering or semantic
change is made.

## Generate-if unpacked-array wall remeasurement

The ranked `generate_if_unpacked_array.sv` fixture is already admitted on the
current tree. Approved extraction and ordinary census report zero refusals.
Canonical E matches Icarus Verilog 13.0 and Xcelium 24.03-s004 for all eight
cycles at N1 and N2, including x/z rows. The prior `GenerateIf: UnpackedDecl`
ranking row is stale; no generate lowering, memory semantic change, or
real-design count transition is claimed.

## Child-instance urgent wall remeasurement

The urgent `child_instance_scan.sv` handoff is already cleared on the current
tree. Approved extraction and ordinary census report zero refusals for the
nested generated `child_instance_scan -> scan_chain -> scan_leaf` hierarchy.
The checked-in canonical-E receipt matches four source rows on Icarus Verilog
13.0 and Xcelium 24.03-s004. No hierarchy lowering or semantic change is
needed; the real present=4 row is stale pending the next full source-overlay
table refresh.

## Urgent port-connection target wall remeasurement

The urgent `port_connection_target_struct_array.sv` fixture retains
`PortConnection:target` at extraction and ordinary E, with the typed aggregate
member boundary following it. Ordinary census refuses at `parsePConn` before
canonical E. The checked-in receipt reports four x/z rows matching Xcelium
24.03-s004. Icarus Verilog 13.0 rejects the unpacked-struct syntax, so no
Icarus oracle result is claimed. No port-target lowering or aggregate
connection semantics is added here.

## Urgent interface-instance wall remeasurement

The urgent `interface_repro.sv` fixture retains interface-instance, interface
port, and interface-port-connection nodes in approved extraction. Ordinary E
reports the exact `GenItem.expand` interface-instance boundary and refuses at
`PDesign.instantiateE2`. The checked-in receipt matches four x/z rows on
Xcelium 24.03-s004; Icarus Verilog 13.0 rejects the interface-port syntax, so
no Icarus oracle is claimed. No interface lowering or connection semantics is
added here.

## Urgent interface-port wall remeasurement

The urgent interface-port row is explicitly predicted in the current
collect-all table: approved extraction retains `InterfacePortSymbol:InterfacePort`
for `interface_repro.sv`, but ordinary admission stops earlier at the
interface-instance boundary and emits no distinct interface-port refusal. The
same four Xcelium 24.03-s004 rows and Icarus syntax limitation recorded for
the fixture therefore apply; no separate ordinary result or interface-port
semantics is claimed.

## Urgent interface-port-connection wall remeasurement

The urgent interface-port-connection row is distinct in the same
`interface_repro.sv` fixture: approved extraction retains
`PortConnection:InterfacePortSymbol`, and ordinary E emits
`parsePConn: <interface port connection>` before the interface-instance E
boundary. The four Xcelium 24.03-s004 x/z rows and Icarus syntax limitation
remain as recorded for this fixture. No interface connection lowering or
semantic admission is added.

## Urgent internal-clock-source wall remeasurement

The urgent `internal_clock_repro.sv` fixture retains a posedge process driven
by `generated_clock`, which an `always_comb` computes inside the module.
Ordinary census emits the exact `Clock:source` refusal at
`PDesign.clockReport`; canonical E then refuses with the `Event:time-zero`
§9.2.2.2/§9.6 settled-start boundary. The five-row receipt matches Icarus
Verilog 13.0 and Xcelium 24.03-s004. No derived-clock scheduling or hardware
glitch semantics is added.

## Urgent multiple-edge-clock wall remeasurement

The urgent `multi_clock_domain.sv` fixture has two independent input clocks.
Ordinary run2 census emits the exact `Clock:multiple` refusal from
`PDesign.clockReport`, preserving the one-clock route's sound boundary. The
direct canonical-E receipt matches eight separate, coincident, stopped, and
x/z clock rows on Icarus Verilog 13.0 and Xcelium 24.03-s004 without selecting
an interleaving. No multi-clock scheduler or hardware clock-domain claim is
added.

## Urgent delay-control wall remeasurement

The urgent `event_always_repro.sv` fixture retains `TimedStatement:DelayControl`
for `#1 q <= d;` in approved extraction and ordinary census at `parsePStmt`.
Its four-row receipt matches Icarus Verilog 13.0 and Xcelium 24.03-s004. The
zero-delay canonical-E route keeps this timing-control boundary loud; no delay
approximation or scheduler timing semantics is added.

## Urgent event-controlled-process wall remeasurement

The urgent event-control clean-room fixture retains a source-level event
process without a supported edge route. Ordinary census emits the exact
`Clock:implicit` refusal at the parser/design boundary, while its four-row
receipt matches Icarus Verilog 13.0 and Xcelium 24.03-s004. No event-list
sensitivity scheduler or source reinterpretation is added.

## Urgent hierarchical-value wall remeasurement

The urgent `hierarchical_value_repro.sv` fixture reads `u.internal_value`
through a child instance. Ordinary census emits the exact
`HierarchicalValueExpression / parsePExpr` refusal. Its two-row receipt
matches Icarus Verilog 13.0 and Xcelium 24.03-s004. No hierarchical-name
resolution or source lowering is added.

## Urgent initial-process wall remeasurement

The urgent `initial_storage_repro.sv` fixture is admitted by the current
canonical-E route: approved extraction and ordinary census report zero
refusals, and its two-row receipt matches Icarus Verilog 13.0 and Xcelium
24.03-s004. The legacy Design2/run2 initial-process boundary remains a
separate route refusal; no runtime-initial lowering or new scheduler meaning
is added here.

## Resolved-net real-design remeasurement

After the canonical IEEE 1800-2023 §6.6 driver-resolution landing, the pinned
`prim_packer` source overlay retains structured metadata for the two generated
`ready_o` drivers.  The live net-z boundary is therefore no longer the first
admission failure in this current envelope.  `load_design_sv2` reaches the
existing packed-enum check first and refuses with `enum 'flush_st_e':
unrecoverable packed dimensions`.  Canonical E does not execute this complete
design, and no real-design count transition is claimed.  The checked-in
resolved-net receipt remains the executable semantic evidence for the four
known, conflicting, and x/z driver rows against Icarus Verilog 13.0 and
Xcelium 24.03-s004.

## Generate-local census correction after the upstream rebase

The earlier blocked census entry was caused by a stale checkout that lacked
the upstream `GenItem.localParam` constructor.  After rebasing onto the
current public master, the ordinary census compiler builds and the checked-in
`generate_parameter_e` envelope reports zero refusals.  Fresh extraction and
ordinary census of the clean-room `generate_parameter.sv` and
`packed_enum_package_repro.sv` fixtures also report zero refusals.  The
generate-parameter receipt runs W=8 and W=3 for eight cycles each, with every
cycle matching Icarus Verilog 13.0 and Xcelium 24.03-s004, including the x/z
rows.  No real-design count transition is claimed by this remeasurement.

## Typed aggregate/member wall ownership

The current ls-sv3 handoff requests ownership of the shared aggregate relation
for typed ports, unpacked aggregate storage, typedef-backed records, and nested
member paths.  Current ordinary census measurements retain the parser-native
`PortSymbol:type`, `VariableSymbol:type`, `TypeAliasType:TypeAlias`, and
`MemberAccessExpression` boundaries.  The canonical route then refuses typed
module members or the reactive dependency order, so no field flattening is
sound.

The shared relation belongs to the general lane because it changes canonical
E's state and step judgments.  ls-sv3 remains the owner of its extractor and
ordinary-route wall fixtures.  The current clean-room rows are `typed_nested_repro.sv`
with `PortSymbol:type` and `VariableSymbol:type`, `type_alias_nested_repro.sv`
with `TypeAliasType:TypeAlias` and the dependency-order refusal, and
`member_nested_repro.sv` with `MemberAccessExpression` followed by the typed
storage refusal.  No aggregate count transition is claimed.

## Current ordinary wall-table correction — 2026-11-18T04:15Z

Fresh ordinary census at the current public head confirms the rows previously
marked predicted. `primitive_repro.sv` reaches and refuses
`PrimitiveInstanceSymbol:PrimitiveInstance` in `PDesign.instantiate`, then
reports the same boundary from `PDesign.instantiateE2`. `specify_repro.sv`
similarly reaches and refuses `SpecifyBlockSymbol:SpecifyBlock`. The typed
aggregate rows are measured rather than predicted: `typed_nested_repro.sv`
retains `PortSymbol:type` and `VariableSymbol:type` and reaches the canonical
typed-storage E boundary, while `member_nested_repro.sv` retains
`MemberAccessExpression:aggregate` after the extractor update. These are
ordinary loud boundaries. No REAL-BLOCKS or E-ROWS count transition is claimed.

## Current-head package remeasurement — 2026-11-18T02:00Z

At public master d97c9b19e9836c1aaff4524eb39f02281d5bc4b, the approved
ordinary-route census was rerun for the twelve fixtures in this package. The
refusal-free fixtures are net_z_generated_repro.sv, wire_output_port.sv,
generate_parameter.sv, generate_local_hierarchy.sv, constant_width_conversion.sv,
packed_enum_package_repro.sv, and typed_unpacked_net.sv. The retained loud
boundaries are PortSymbol:InOut and PortConnection:InOut for inout_repro.sv,
PrimitiveInstanceSymbol:PrimitiveInstance for primitive_repro.sv,
SpecifyBlockSymbol:SpecifyBlock for specify_repro.sv, the typed named-value
aggregate chain for typed_named_unpacked.sv, and the unconditional generate
items for unconditional_case2.sv. The results match the previously recorded
IEEE 1800-2023 wall matrix. No SV implementation paths changed between the
package landing and this head, so REAL-BLOCKS remains 41 and no count
transition is claimed.

## Full clean-room batch census — 2026-11-18T03:25Z

The required external `CENSUS-ls-sv3.txt` was refreshed with the approved
single-harness command at public master 4338b0c82. The batch measured 58
fixture/parameter points. Forty-eight returned eight ordinary cycles, while
ten returned ordinary zero for the named dependency-order, LocalDecl,
non-literal initializer, Clock:implicit, untyped-localparam, 10.3, and
parameterized-storage equation-gate boundaries. Icarus Verilog 13.0
(`s20250103-64-gdad78d525`) and Xcelium 24.03-s004 were both detected. The
receipt printed 768 ordinary/source matching cycles and 72 source-only matching
cycles for intentionally refused ordinary routes. REAL-BLOCKS remains 41.

## Aggregate relation landing remeasurement — 2026-11-18T02:52Z

After public landing 8ade780f5 added the source-shaped aggregate relation, fresh
ordinary censuses of typed_nested_repro.sv, typed_named_unpacked.sv,
member_nested_repro.sv, and type_alias_nested_repro.sv were rerun. The typed
port and variable, typed named-value, member-access, and type-alias parser nodes
remain preserved. Ordinary E still ends at the canonical typed-port or typed
variable storage boundary, with the type-alias case retaining the
9.2.2.2/9.4.2.2 dependency-order refusal. No aggregate wall moved and
REAL-BLOCKS remains 41.

## Package-head reconciliation — 2026-11-18T02:19Z

The current public head remains 9f0f4cbf5 after the output-net-z
remeasurement. No newer inbox handoff or SystemVerilog implementation commit
is present. The package's current fixture receipts and corrected output-net-z
classification are therefore authoritative, with REAL-BLOCKS unchanged at 41.

## Member-access current-head check — 2026-11-18T02:16Z

Fresh extraction of member_nested_repro.sv at public master 2ef87c779 retains
VariableSymbol:type and MemberAccessExpression for state.words[i].value.
Ordinary E reports the member access at parsePExpr and then refuses the
aggregate variable module member. IEEE 1800-2023 section 11.8 member-path
semantics depend on unpacked aggregate storage absent from canonical E, so no
field lowering is introduced. Existing Xcelium 24.03-s004 rows report xxxx;
Icarus Verilog 13.0 rejects unpacked structs. No count transition is claimed.

## Type-alias current-head check — 2026-11-18T02:15Z

Fresh extraction of type_alias_nested_repro.sv at public master 40426e6f6
retains VariableSymbol:type and TypeAliasType:TypeAlias. Ordinary E retains
both parser-native nodes and refuses at the reactive dependency-order boundary
for state.field.value. IEEE 1800-2023 sections 9.2.2.2 and 9.4.2.2 require
scheduling semantics that canonical E does not model, so no alias lowering or
fixed-point approximation is introduced. Existing four-state source receipts
remain the simulator evidence. No count transition is claimed.

## Unconditional-generate current-head check — 2026-11-18T02:13Z

Fresh extraction of unconditional_case2.sv at public master bc8059b74 retains
two GenerateBlockSymbol:unconditional nodes. Ordinary E reports both source
assignments at GenItem.expand and PDesign.instantiateE2, then refuses the
module members. IEEE 1800-2023 section 27.4 requires source-shaped generate
item semantics, so no unrolling is introduced. Existing Icarus Verilog 13.0
and Xcelium 24.03-s004 rows agree on 00, 11, and xx. No count transition is
claimed.

## Typed port and variable current-head check — 2026-11-18T02:14Z

Fresh extraction of typed_nested_repro.sv at public master 03009269d retains
PortSymbol:type, VariableSymbol:type, and the source-shaped assignment target.
Ordinary E retains those parser-native boundaries and refuses the typed port
module member at instantiateE2. IEEE 1800-2023 section 6.8 aggregate
port/member layout remains outside the flat E storage relation, so no field
flattening or variable lifting is introduced. Existing Xcelium 24.03-s004
rows report 0->0000, x->xxxx, z->zzzz, and f->1111; Icarus Verilog 13.0
rejects unpacked structs. No count transition is claimed.

## Specify-block current-head check — 2026-11-18T02:11Z

Fresh extraction of specify_repro.sv at public master f2377936d retains
SpecifyBlockSymbol:SpecifyBlock. Ordinary E reports the node at
PDesign.instantiate and refuses it in instantiateE2. IEEE 1800-2023 section
30 defines timing paths and checks, while canonical E is zero-delay and has no
timing scheduler, so the timing construct remains a loud refusal. Functional
rows match Icarus Verilog 13.0 and Xcelium 24.03-s004 in the existing receipt.
No count transition is claimed.

## Generate-variable current-head check — 2026-11-18T02:55Z

Fresh extraction and ordinary census of generate_local_hierarchy.sv at public
master 604d35553 report zero refusals. The source-shaped generate-scope
variable remains admitted through canonical E lexical scope under IEEE
1800-2023 section 27.4. Existing N=1 and N=4 eight-cycle receipts match
Icarus Verilog 13.0 and Xcelium 24.03-s004, including x/z rows. No count
transition is claimed.

## Resolved net-with-z current-head check — 2026-11-18T02:17Z

Fresh extraction of resolved_net_multiple_driver.sv at public master 2907217f2
retains PortSymbol:net-z. Ordinary E reports that parser-native net at
PDesign.instantiate and refuses the module member in instantiateE2. IEEE
1800-2023 section 6.6 requires four-state driver resolution for conflicting
drivers, so canonical E keeps a loud refusal rather than collapsing drivers.
Existing Icarus Verilog 13.0 and Xcelium 24.03-s004 rows agree on y=x. No
count transition is claimed.

## Output net-with-z current-head check — corrected 2026-11-18T03:40Z

Fresh extraction of wire_output_port.sv retains PortSymbol:net-z for y. The
ordinary census always prints retained parser-native design rows through
PDesign.instantiate, even when canonical E admits the design. The authoritative
batch receipt reports ordinary=8 for this fixture, with all eight undriven
output bits reading z and matching Icarus Verilog 13.0 and Xcelium 24.03-s004.
IEEE 1800-2023 section 6.6 is therefore admitted for this complete undriven
output-net shape. The earlier refusal classification was a census-reading
error and is superseded. No count transition is claimed.

## Typed named-value current-head check — 2026-11-18T02:12Z

Fresh extraction of typed_named_unpacked.sv at public master 770931a50 retains
VariableSymbol:type, NamedValueExpression:type, and PortSymbol:type. Ordinary
E reports the named value at parsePExpr, the aggregate variable boundary at
PDesign.instantiate, and then refuses the typed port module member. IEEE
1800-2023 section 6.8 aggregate named-value and member-layout semantics remain
outside the flat E storage relation. Existing Xcelium 24.03-s004 rows report
xxxx; Icarus Verilog 13.0 rejects unpacked structs. No flattening or count
transition is claimed.

## Primitive-instance current-head check — 2026-11-18T02:10Z

Fresh extraction of primitive_repro.sv at public master 31561db80 retains
PrimitiveInstanceSymbol:PrimitiveInstance. Ordinary E reports the primitive
at PDesign.instantiate and then refuses it in instantiateE2. IEEE 1800-2023
section 28 gives primitive instances dedicated cell semantics, so canonical E
keeps a loud refusal rather than lowering the gate to an assignment. The
faithful output-logic source remains simulator-asymmetric between Icarus
Verilog 13.0 and Xcelium 24.03-s004; the existing wire-terminal receipt agrees
on both. No count transition is claimed.

## Current-head reconciliation — 2026-11-18T02:05Z

Public master advanced from 2c1750717 to eaa90b1219a6f4453132adbec039b3032f64a722.
The intervening commit changes only the Python machine implementation and
does not touch the SystemVerilog extractor, loader, hierarchy, ingestion,
canonical-E, structure, or equations paths. The twelve-fixture package census
and the 57-row wall matrix therefore remain current. REAL-BLOCKS remains 41,
with no SV count transition.

## Generate-local parameter current-head check — 2026-11-18T02:06Z

Fresh Slang extraction and ordinary census of generate_parameter.sv at public
master a97604716 report zero refusals. The source-shaped generate-local
parameter remains admitted through canonical E lexical scope under IEEE
1800-2023 section 27.4. The existing W=8 and W=3 receipts match Icarus
Verilog 13.0 and Xcelium 24.03-s004, including x/z rows. No count transition
is claimed.

## Packed-enum dimensions current-head check — 2026-11-18T02:07Z

Fresh Slang extraction and ordinary census of packed_enum_package_repro.sv at
public master 2ce6e831b report zero refusals. The scalar package enum passes
the packed-dimension and cross-check boundaries under IEEE 1800-2023 section
6.19. Its existing eight-row receipt matches Icarus Verilog 13.0 and Xcelium
24.03-s004 for the 4-state rows. No count transition is claimed.

## Typed net current-head check — 2026-11-18T02:08Z

Fresh Slang extraction and ordinary census of typed_unpacked_net.sv at public
master 46362fb43 report zero refusals. The fixed unpacked typed net remains
admitted by the canonical storage representation under IEEE 1800-2023 section
6.8. Existing eight-cycle ordinary/source rows match Icarus Verilog 13.0 and
Xcelium 24.03-s004, including x/z inputs. The former NetSymbol:type wall is
cleared and no count transition is claimed.

## Inout port and connection current-head check — 2026-11-18T02:09Z

Fresh extraction of inout_repro.sv at public master 8a18aed91 retains
PortSymbol:InOut on both ports and PortConnection:InOut at the child
connection. Ordinary E reports parsePConn and PDesign.instantiate boundaries,
then refuses the PortSymbol:InOut module member. IEEE 1800-2023 sections 6.6
and 23.2.2 require resolved bidirectional driver semantics, including x/z and
conflicts, which canonical E does not model. The existing source receipt
matches Icarus Verilog 13.0 and Xcelium 24.03-s004. No lowering or count
transition is claimed.
## Current-head resolved-net wall correction

Fresh extraction of the clean-room `resolved_net_multiple_driver.sv` fixture
with the current Slang frontend retains both dynamic continuous assignments as
`Assign` nodes with `continuous_net_target: true`.  The stale checked-in
envelope's second `AssignmentExpression:target` marker is therefore no longer
evidence for the current extractor.  The ordinary census reaches the intended
`PortSymbol:net-z` boundary for output `y`, where structured metadata keeps
both generated driver records.  No canonical-E execution or real-design count
transition is claimed by this correction.

## Stall-rule wall ranking after the current-head remeasurement

The three preceding items changed no E-ROWS or REAL-DESIGNS count, so the
current clean-room matrix was re-ranked by breadth and ownership.  The next
general-lane wall is the shared aggregate/member relation, whose typed ports,
typed variables, aliases, named values, and member paths cover six to seven
real-module closures and change canonical E state and step judgments.  The
event-controlled procedural block is the next broad scheduler wall at eight
closures, followed by child-instance hierarchy at four closures, while net-z
module members and packed-enum dimensions remain ls-sv3-owned boundaries.  The
resolved-net multiple-driver row is now a focused `PortSymbol:net-z` boundary
with both driver records retained.  No count transition is claimed.  The next
item is therefore the shared aggregate relation, beginning with the typed
clean-room state representation and its refinement obligations.

## Generated net-with-z current-head check — 2026-11-18T02:53Z

Fresh extraction of net_z_generated_repro.sv at public master c72eb6bbd
retains NetSymbol:net-z for the undriven four-state net. Ordinary E reports
zero refusals, so the generated-net startup metadata is admitted through the
canonical net representation. Existing ordinary/source rows match Icarus
Verilog 13.0 and Xcelium 24.03-s004, including z startup and x/z propagation.
No count transition is claimed.

## ls-sv3 package closure audit — 2026-11-18T02:56Z

After rereading the lane inbox, the current OVERVIEW.txt table contains 15
ADMIT rows owned by ls-sv3. Each has a named fixture and a current measured or
predicted status, and the package receipts cover all 15 families, including
the corrected output-net-z and resolved-net cases. No unmeasured ls-sv3-owned
wall remains. The next broad wall is the shared aggregate/member relation
owned by the general lane. REAL-BLOCKS remains 41.

## Stall-rule wall ranking after aggregate-boundary landing — 2026-11-18T04:02Z

The aggregate/member packet added parser-native field and bound metadata but
did not move E-ROWS or REAL-DESIGNS, so the remaining matrix was re-ranked by
breadth and ownership. Event-controlled procedural blocks remain the broadest
general-lane wall at eight real-module closures. The aggregate storage and
member-step semantics are the next general-lane dependency after the landed
metadata boundary, followed by hierarchical value expressions at seven,
interface ports and connections at six, initial processes and delay controls at
five, child instances and multiple clocks at four, and derived internal clocks
at three. Net-z members and packed-enum dimensions remain ls-sv3-owned. No
count transition is claimed; the next implementation item is the
event-controlled scheduler boundary.

## Aggregate-shape landing remeasurement — 2026-11-18T05:00Z

After public landing 0701d9066, the four aggregate fixtures were rerun through
the approved extractor and ordinary census. typed_nested_repro.sv now retains
the parser-native MemberAccessExpression:aggregate marker alongside its typed
port and variable boundaries. type_alias_nested_repro.sv retains the same
aggregate member marker and reaches the typed variable E refusal. The named
value and nested member fixtures retain their typed aggregate boundaries. The
canonical E route still refuses PortSymbol:type or VariableSymbol:type, so
REAL-BLOCKS remains 41 and no aggregate admission transition is claimed.

## Typed aggregate store landing remeasurement — 2026-11-18T05:30Z

After public landing 5fcf45f6f, the four aggregate fixtures were rerun through
the approved extractor and ordinary census. The new aggregate store relation
preserves `MemberAccessExpression:aggregate` and the source-shaped typed
declarations. `typed_nested_repro.sv` and `typed_named_unpacked.sv` still end
at the `PortSymbol:type` E refusal. `member_nested_repro.sv` and
`type_alias_nested_repro.sv` still end at the `VariableSymbol:type` E refusal.
No fixture crosses the aggregate storage boundary, so REAL-BLOCKS remains 41.

## Scalar event-control landing remeasurement — 2026-11-18T06:00Z

After public landing f8622b3f9, the event-control fixtures were rerun. The
source-shaped `event_control_repro.sv` ordinary census is refusal-free, and
its pinned seven-row canonical-E receipt matches Icarus Verilog 13.0 and
Xcelium 24.03-s004. `signal_event_control.sv` remains a `Clock:implicit`
refusal because its event source has no supported edge or implicit-sensitivity
semantics. No count transition is claimed.

## Parser-native inout wall reconciliation — 2026-11-18T18:05Z

The clean-room `inout_repro.sv` packet is now represented source-shaped in the
public loader. Slang's `PortSymbol:InOut` direction is retained as `PDecl.isInout`,
and its child connection is retained as `PConn.inout`, including assignment-form
actuals. Canonical scalar E and both hierarchy adapters still refuse at the
IEEE 1800-2023 §6.6 driver-set resolution boundary. The independent receipt
reports six matching rows from Icarus Verilog 13.0 and Xcelium 24.03-s004,
covering all-known, high-impedance, and conflicting drivers. No aliasing,
flattening, or scalar x/z approximation is claimed. The parser-native landing
is public in `0f7f84270`, and the aggregate-member red-fix ancestry was pushed
without waiting for the asynchronous-memory profile wall.

## CV32E40P package x/z constant wall — 2026-11-18

The next CV32E40P load wall is a parser-native package parameter default with
25 `z` bits and the `INSTR_LUI` opcode.  The clean-room receipt
`Examples/system-verilog/sem2/package_param_xz_wall/check.py` regenerates its
envelope byte-identically, and the canonical loader records the exact refusal
`defaults: package parameter 'package_param_xz_wall_pkg::INSTR_LUI': x/z literal
in a constant context`.  Icarus Verilog 13.0 and Xcelium 24.03-s004 both
produce the source row `zzzzzzzzzzzzzzzzzzzzzzzzz0110111`.  No integer
reinterpretation or package-constant semantic change is claimed.  The trusted
package binding remains an explicit four-state representation decision for the
lead.

## Current-head wall ranking — 2026-11-18T21:56Z

The current public admission table remains 3 designs loading and 4 refused,
with no E-ROWS or REAL-DESIGNS transition in the last three items. The highest
independent wall is CV32E40P's package parameter default containing z bits,
which needs an explicit trusted four-state package-binding representation. The
next source-shaped loader wall is Ibex's packed enum dimension recovery, then
OpenTitan's scoped procedural `LocalDecl`; both are assigned to the parameter
and local-storage families. PicoRV32 and DarkRISCV now have source-shaped
one-rank memory receipts, while their remaining whole-core blockers are
execution cost and clocked storage targets. The inout and latch target families
remain explicit canonical-E refusals with matching pinned-simulator rows. This
ranking is based on the generated `docs/sv-real-designs.md` check and the
package x/z receipt, not a new real-design count claim.

## Parameter-default assignment-pattern wall — 2026-11-19

The pinned Ibex remeasurement reaches the parser-native `AssignmentPattern:default-point`
value in a package/module parameter default. The clean-room receipt
`Examples/system-verilog/sem2/assignment_pattern_param_e/` now retains the
`'{default: 4'h0}` node and runs its fixed packed-array value through canonical
E. This follows IEEE 1800-2023 §10.9's aggregate-pattern correspondence rule
without freezing a parameter-dependent width at the default point.

Canonical E and Xcelium 24.03-s004 produce three rows, `0000`, `1010`, and
`xxxx`. Icarus Verilog 13.0 rejects the faithful parameter-default syntax, so
no Icarus oracle result is claimed. The pattern is represented as a four-state
concat, never as a scalar integer. Parameter-dependent packed widths remain
loud. This clears the fixed-width row while retaining the exact
default-point boundary for the unresolved family.

## Package-enum symbolic dimensions — 2026-11-18

The extractor now resolves packed-enum dimension identifiers in the
parser-owned package scope. A package enum such as
`typedef enum logic [W-1:0] {PA = 0, PB = 1} p_t` retains `W` as a
source-shaped `ParamRef` with package provenance, alongside the elaborated
width as secondary metadata. This removes the earlier
`Syntax:Identifier:unresolved` ingestion loss without changing the enum's
four-state value semantics or claiming a canonical-E row. The regression
covers the parameterized package enum and the existing symbolic enum suite.

## Stall-rule ranking after public-head remeasurement — 2026-11-19

The checked-in REAL-DESIGNS generator remains consistent at the current public
head. The seven pinned designs still have three loader successes and four
refusals. The first walls are `Constant: $bits` for `prim_fifo_sync`, scoped
procedural `LocalDecl` for `prim_arbiter_ppc`, packed-enum dimensions for
`prim_packer`, retained edge semantics for CV32E40P, and `AlwaysLatch` for
Ibex. PicoRV32 still reaches its bounded input-driven E-RUN limit after the
time-zero pass, while DarkRISCV still reaches the dynamic register-memory
target wall. The next independent implementation wall is the OpenTitan
`$bits` constant-context case, followed by scoped local storage. The package
enum change is parser-side only, so no REAL-DESIGNS transition is claimed from
it without a fresh pinned-source envelope and loader receipt.

## Stall-rule ranking after 2026-11-20 real-design measurements

The current public head still has three designs loading and four refused, with
no E-ROWS or REAL-DESIGNS count transition across the last three completed
items.  The pinned OpenTitan `prim_fifo_sync` source now reaches canonical-E
hierarchy admission and its first independent runtime walls are the
parser-native `SysCall:$error` and `TimedStatement:DelayControl` nodes.  The
CV32E40P envelope loads at `(C_WIDTH, C_LOG_WIDTH) = (8, 3)` with 26 retained
processes and `Structure=true`; its next boundary is `EquationGate=false` at
the sole retained `always_comb` process (index 10, the `State_SN`, `OutVld_SO`,
and enable assignments selected by `case (State_SP)`).  The highest-value
remaining walls are therefore, in order, a source-shaped diagnostic channel
for `$error` with its IEEE 1800-2023 §20.10 observability contract, a timed
event-region representation for delay control, and a general equation theorem
for procedural `always_comb` bodies.  No count transition is claimed from
this ranking, and no wall is admitted by weakening the existing refusal or
equation-gate obligations.

The existing diagnostic-only initial-check adapter was remeasured before
changing this boundary.  The source-shaped `initial_parameter_check` witness
matches Icarus Verilog 13.0 and Xcelium 24.03-s004 at both `N=1` and `N=0`
for all eight observed cycles.  The failing `N=0` point also records
Xcelium's expected assertion diagnostic while canonical E preserves the
`y=0` state.  This confirms the admitted subset for elaboration-time checks
and does not clear the general `prim_fifo_sync` `$error` wall, which remains
outside that subset.

The paired source-shaped `initial_delay_check` receipt at
`Examples/system-verilog/sem2/initial_delay_check_e/` likewise matches
Icarus Verilog 13.0 and Xcelium 24.03-s004 on all eight observed cycles.  Its
literal `#1` occurs only in an initial diagnostic check, so the canonical E
adapter preserves the `assign y = x` state while treating the diagnostic-only
delay as outside the state observation.  This does not admit general
`TimedStatement:DelayControl` processes or advance `prim_fifo_sync`'s wall.

## Post-R14 generate-loop event remeasurement — 2026-11-20T19:51Z

The source-shaped `plain_generate_edge_e` receipt was rerun after the R14
substitution landing. Slang re-extraction reproduces the checked-in envelope,
the ordinary census reports zero refusals, and canonical E, Icarus Verilog
13.0, and Xcelium 24.03-s004 match all eight rows, including x/z clock and
data values. This clears the explicit `AlwaysEvent` inside `GenerateFor`
family for the retained-process route and does not lower or unroll the source.

The checked-in pinned real-design table is unchanged by this clean-room
receipt, so no REAL-DESIGNS count transition is claimed. The current
clean-room overview still identifies generate-loop expansion as the first
clocked wall for its two unavailable real-design probes. One probe exposes a
memory-topology boundary after that wall, while the other remains at the
same generate-loop refusal. Those observations remain a ranking input rather
than an admission claim until their source-shaped envelopes are available to
this tree.

## Stall-rule ranking after canonical receipt repairs — 2026-11-20T20:23Z

The current clean-room overview has advanced past the earlier generate-loop
snapshot. Its latest real-source checks report FIFO loading ten processes and
one memory before a deterministic symbolic-elaboration timeout, handshake
reaching an internal time-zero event wall before child hierarchy and
multi-clock structure, an integer multiplier loading 28 processes before a
level-event instantiation timeout, and Kogge–Stone loading 29 processes and
two memories before its declared-output memory target on the first run. The
fixed-width float reduction remains at the mixed `always_comb` beside
flip-flops profile refusal. These are measured ranking inputs only. No
REAL-DESIGNS count transition is claimed, and no timed, memory, or equation
semantics is admitted by this refresh.

## Current-head wall ranking after mixed-trace reconciliation — 2026-11-20T20:26:13Z

The current public head is `db6702c0d0d64c7bdd41b430b2ba482cbb59ec67`, and the generated `docs/sv-real-designs.md` census remains three designs loading into E and five rows with no load transition in the checked-in table. The latest overview reconciliation adds mixed async-reset tracing and plain generate-event substitution, while the affected int-to-float source still reaches deterministic symbolic structure timeout. The highest measured real-source walls remain FIFO's symbolic elaboration timeout after ten processes and one memory, handshake's internal time-zero event wall, the integer multiplier's level-event instantiation timeout after 28 processes, Kogge–Stone's declared-output memory target after 29 processes and two memories, and the fixed-width float reduction's mixed `always_comb` beside flip-flops refusal. These measurements change no E-ROWS or REAL-DESIGNS count. Timed, memory, equation, and mixed-profile semantics remain deferred until each has a source-shaped contract and pinned-simulator receipt.

## Runtime `$error` refusal receipt — 2026-11-20T20:35:16Z

The source-shaped `initial_error_refuse.sv` fixture retains a runtime `$error` system task in an `initial` process beside `assign y = x`. Canonical E's ordinary census reports the exact refusal `SysCall:$error`; its parser-native process and assignment nodes remain visible in the checked-in envelope. Icarus Verilog 13.0 and Xcelium 24.03-s004 both emit the expected diagnostic and agree on all four four-state output rows, `y=0`, `y=x`, `y=z`, and `y=1`. This receipt confirms the current wall at IEEE 1800-2023 §20.10 diagnostic observability and does not admit runtime task execution or change E-ROWS or REAL-DESIGNS.
