# Choice-explicit step rows

`rows.lean` lifts the 23 probe rows used in the relation review into the
repository. It checks the loaded `simultaneous_nba` design at `begin`, `fire`,
`commit`, `ndStep`, and the refusal boundaries. Rows R7-R13 cover the two
legal swap schedules, the executor result, the disabled choice, and the
hand-built blocking-write race. Rows R14-R17 and R23 check the named refusal
messages. Rows R19-R22 check the two oracle branches and the existing
four-state ternary and operand-merge boundaries.

R18 now checks that an equality observer inside a write index is refused before
the leaf evaluator. R24 and R25 check the binary `casez` and `casex` observer
forms, with the named IEEE 1800 §12.5.4 refusal.

`check.py` runs the source-shaped arm witnesses through Icarus Verilog 13.0
and Xcelium 24.03-s004 when available. Both simulators produce all 25 rows.
The two blocking-write race rows intentionally show the simulator-specific
active-region order, Icarus producing 0 then 1 and Xcelium producing 1 then 0.
This is a declared simulator disagreement for the race rows, so no single
oracle value is claimed there. The remaining 23 rows match exactly. The simulator values document the source
behavior around the relation's explicit refusal boundaries and do not replace
the relation rows.
