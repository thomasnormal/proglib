# Generated dynamic output-net driver in canonical E

This clean-room shape exercises the `prim_fifo_sync` wall's source form: one
active conditional-generate branch drives a full-width output wire from a live
expression. The structured Slang driver record is admitted as a net variable,
while the source-shaped assignment remains the E process. IEEE 1800-2023 §6.6
still gives the declaration a z startup value before its driver settles.

The four known input rows match canonical E and Icarus Verilog 13.0.
