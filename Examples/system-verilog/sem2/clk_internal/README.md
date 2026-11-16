# Internal clock refusal

The continuous-copy clock `ck` is refused by the ordinary clock discipline
and by canonical E. The latter reports `Clock:source: clock 'ck' is not a
top-level input port; canonical E refuses NBA-caused internal clock events
under IEEE 1800-2023 §§4.4 and 9.4.2`. `check.py` compares ten x/z rows on
Icarus Verilog 13.0 and Xcelium 24.03-s004.
