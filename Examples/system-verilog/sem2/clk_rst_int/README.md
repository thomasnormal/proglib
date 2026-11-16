# Internal asynchronous reset refusal

The register-driven reset `rst_q` is refused by the ordinary clock discipline
and by canonical E. The latter reports `Clock:reset: asynchronous reset 'rst_q'
is not a top-level input port; canonical E refuses NBA-caused internal reset
events under IEEE 1800-2023 §§4.4 and 9.4.2`. `check.py` compares ten x/z
rows on Icarus Verilog 13.0 and Xcelium 24.03-s004.

Canonical E B3 now iterates NBA-caused edge events in the same slot. The direct `b3_probe.lean` receipt exercises the register-driven reset: the first clock NBA changes `rst_q`, the asynchronous reset process fires in that same slot, and the four-row q trace passes. The ordinary loader remains a `Clock:reset` refusal.
