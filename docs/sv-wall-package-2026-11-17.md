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

The hierarchical-value repro was measured next. Both extractor and ordinary
collect-all retain `HierarchicalValueExpression` at `parsePExpr` for the
generic `u.internal_value` read. The existing hierarchy flattener handles
parser-native port connections, but it does not invent semantics for an
arbitrary hierarchical value expression (§23.6); the loud refusal remains
sound and the real-design present=7 count is unchanged.
