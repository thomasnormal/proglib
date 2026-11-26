# Choice-explicit step rows

`rows.lean` lifts the 23 probe rows used in the relation review into the
repository. It checks the loaded `simultaneous_nba` design at `begin`, `fire`,
`commit`, `ndStep`, and the refusal boundaries. Rows R7-R13 cover the two
legal swap schedules, the executor result, the disabled choice, and the
hand-built blocking-write race. Rows R14-R17 and R23 check the named refusal
messages. Rows R19-R22 check the two oracle branches and the existing
four-state ternary and operand-merge boundaries.

R18 remains an executable `#eval` gap row. An equality observer inside a write
index currently reaches the leaf evaluator. The next queue item adds the
missing target-index observer walk and turns this row into a named refusal.

`check.py` runs the source-shaped arm witnesses through Icarus Verilog 13.0
and Xcelium 24.03-s004 when available. Both simulators match eight rows. The
simulator values document the source behavior around the relation's explicit
refusal boundaries and do not replace the relation rows.
