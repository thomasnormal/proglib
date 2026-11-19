# Continuous-assign time-zero event-source refusal

These source-shaped probes drive an edge-process event source with a continuous
assignment at time zero. IEEE 1800-2023 §§4.7 and 9.4.2 leave the ordering of the
driver update and the process's first edge wait open. Canonical E now refuses the
shape with `Event:time-zero` instead of selecting one resolution. The refusal
covers both assignment orders.

The differential receipt still runs both pinned simulators. Icarus Verilog 13.0
and Xcelium 24.03-s004 rows are retained as observations of the unresolved race,
without claiming a single oracle value for the active-region scheduling point.
