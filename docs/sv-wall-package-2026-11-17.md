# SV wall package measurement — 2026-11-17

This note records the next ordered wall measurement after the asynchronous-reset
wall.  The asynchronous-reset row is parked: the current public real-design
census reports `present=0`, so there is no live refusal to remove.

The child-instance repro `fleet2/cleanroom/child_instance_scan.sv` was extracted
at the current public head and passed the ordinary collect-all census with zero
refusals.  The native-memory child repro
`fleet2/cleanroom/child_instance_memory.sv` also passed with zero refusals.
These runs exercise the existing source-shaped hierarchy route; they do not
claim that the real-design table's four child-instance modules have moved.

The next ordered port-connection-target repro,
`fleet2/cleanroom/port_connection_target_struct_array.sv`, still reaches the
earlier typed-aggregate boundary first.  Its ordinary census reports
`VariableSymbol:type` for `state` and then
`Instantiation:E:unsupported: E memory route does not yet admit module member
'VariableSymbol:type'`; the extractor also retains `PortConnection:target` for
`out_state`.  The IEEE 1800-2023 §23.2.2 target cannot be admitted faithfully
until the typed struct declaration and member-path semantics are available.
This wall is therefore parked at its measured dependency, with no count
reduction claimed.

The census was run with the repository's `harness/sv/refusal_census.py` and all
gate artifacts were written under `/scratch/thomas-ahle/gate/ls-sv/`.

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
