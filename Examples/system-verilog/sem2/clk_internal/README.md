# Internal clock refusal

The continuous-copy clock `ck` is refused by the ordinary clock discipline
and by canonical E. The ordinary route reports `Clock:source`; canonical E
reports `Event:time-zero` when its always_comb driver would create the clock
before the settled start state, under IEEE 1800-2023 §§9.2.2.2/9.6. `check.py`
compares ten x/z rows on Icarus Verilog 13.0 and Xcelium 24.03-s004.
