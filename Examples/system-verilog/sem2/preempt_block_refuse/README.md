# Preemptive blocking-write refusal receipt

This clean-room shape records the IEEE 1800-2023 §4.7 scheduler boundary. A
multi-write blocking process remains refused by canonical E as
`Schedule:preemptive`, because an admissible suspension can expose an
intermediate write to another process. The unchanged source rows match Icarus
Verilog 13.0 and Xcelium 24.03-s004.

Receipt command

```text
TMPDIR=<scratch> python3 Examples/system-verilog/sem2/preempt_block_refuse/check.py
```
