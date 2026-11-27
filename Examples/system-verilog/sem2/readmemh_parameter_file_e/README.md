# Parameter-selected `$readmemh` file

The source passes an untyped string parameter as the elaboration-time file
name to `$readmemh`.  Under IEEE 1800-2023 §21.4, a missing selected file
leaves the unpacked memory unchanged, so its four-state cells remain `x`.
Canonical E retains the task and models that time-zero state.  Icarus
Verilog 13.0 and Xcelium 24.03-s004 both accept the source and report
`y=xxxxxxxx`.
