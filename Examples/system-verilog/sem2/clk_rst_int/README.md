# Internal asynchronous reset refusal

The register-driven reset `rst_q` is refused by the ordinary clock discipline
and by canonical E's soundness boundaries. The ordinary route reports
`Clock:reset`; canonical E reports the applicable event-source refusal when the
internal reset would be driven outside the settled start state, under IEEE
1800-2023 §§4.4, 9.2.2.2, and 9.6. `check.py` compares ten x/z rows on
Icarus Verilog 13.0 and Xcelium 24.03-s004.

The direct `b3_probe.lean` receipt remains the focused NBA event exercise; the
ordinary loader retains its named `Clock:reset` refusal.
