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
