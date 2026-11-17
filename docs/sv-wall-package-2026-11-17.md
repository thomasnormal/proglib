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
