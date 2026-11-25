# Ibex LockstepOffsetW boundary receipt

The source-shaped package constant function and dependent localparam used by
Ibex `LockstepOffsetW` are evaluated under IEEE 1800-2023 §§13.4 and 20.6.
This isolates the real-design wall from the remaining full Ibex dependency
closure.

The isolated receipt remains current. The full pinned Ibex closure still has
unresolved struct-port, primitive, and dependent-module walls before this
constant-function site can be reached in one ordinary load.
