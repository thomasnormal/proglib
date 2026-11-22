# Scheduler preemption wall receipt

Source-shaped fixture `scheduler_preemptive.sv` was measured with Icarus
Verilog 13.0 (`s20250103-64-gdad78d525`) and Xcelium 24.03-s004. Both
simulators produced the same eight rows for `a`, `b`, `q`, `r`, and `z`.

| simulator | rows | membership |
|---|---:|---|
| Icarus Verilog 13.0 | 8/8 | `q=r=z=0,1,x,z` at the corresponding input rows |
| Xcelium 24.03-s004 | 8/8 | `q=r=z=0,1,x,z` at the corresponding input rows |

The scheduler-side guard checks the settled `a=1,b=0` row and obtains
`q=r=z=1`. The canonical E memory route continues to refuse this source
shape as `Schedule:preemptive` because the first process exposes a blocking
intermediate write to a second process under IEEE 1800-2023 §4.7.

`LeanModels.Sv.Kernel.CoreMemResume` now exposes the parser-native
`CombPhaseStep` relation. Each step chooses one retained `CombCursor`, runs
one source node, and keeps the selected continuation and shared view. The
relation permits every §4.7 interleaving and leaves the canonical refusal
unchanged. The pinned PicoRV32 envelope consumes the same parser-native pair
predicate at all 26 defaults, with 45 non-generated processes and 14 directed
writer/reader pairs recorded by its probe.
