# Generated output-net driver in canonical E

This clean-room shape covers an output `wire` whose only full-width driver is
inside an active conditional-generate branch. Slang's structured driver table
marks the assignment as generated; the extractor retains the port as a net
variable, and canonical E expands the active branch without changing the
source-shaped assignment.

The two rows (`N=1`, initial and clocked probe) match canonical E and Icarus
Verilog 13.0. The Xcelium receipt is readiness-gated and uses the pinned
`xrun(64) 24.03-s004` version when available.
