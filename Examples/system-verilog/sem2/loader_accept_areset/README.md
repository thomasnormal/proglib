# Active-high asynchronous-reset admission

This clean-room source isolates `always_ff @(posedge clk or posedge rst)`.
The ordinary loader admits the retained active-high event form. Canonical E
uses the IEEE 1800-2023 §9.4.2 `posedge` edge table for the reset, including
x/z transitions; active-low reset uses the corresponding `negedge` table.

`agree.lean` checks the structured `resetHigh` process and canonical E
admission. `check.py`
regenerates the Slang envelope, checks ordinary loader admission, and
compares eight x/z-inclusive source rows against Icarus Verilog 13.0 and
Xcelium 24.03-s004.
