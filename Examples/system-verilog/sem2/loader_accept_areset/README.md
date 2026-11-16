# Active-high asynchronous-reset refusal

This clean-room source isolates `always_ff @(posedge clk or posedge rst)`.
The canonical clocked tier currently retains the IEEE 1800-2023 active-low
reset event form; active-high asynchronous-reset scheduling is outside that
profile (§9.4), so the ordinary loader refuses it as `Clock:async-reset`
without approximating the event.

`agree.lean` checks the structured `resetHigh` admission guard. `check.py`
regenerates the Slang envelope, checks the ordinary loader refusal, and
compares eight x/z-inclusive source rows against Icarus Verilog 13.0 and
Xcelium 24.03-s004.
