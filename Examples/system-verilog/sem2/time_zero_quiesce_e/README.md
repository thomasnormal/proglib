# Time-zero continuous-assignment quiescence

These three source-shaped probes exercise the canonical E time-zero active
region. IEEE 1800-2023 §§4.5 and 10.3 allow a continuous assignment to update a
later driver, so the region must run until its view stops changing. The two
edge-source probes also expose the §4.7 ordering boundary at time zero.

Before the fix, the route took one source-order pass. The non-topological chain
then had `a=x,b=1`, and the two edge-source designs differed by assignment
order. The quiesced route has `a=1,b=1`. The edge-source designs are now refused before
execution because a continuous assignment and the first edge wait share time zero
(IEEE 1800-2023 §§4.7 and 9.4.2). This keeps both possible scheduling resolutions
out of canonical E until the event queue is modeled. Icarus Verilog 13.0 and Xcelium 24.03-s004 agree on the settled row. Their
delta-cycle observations differ for the non-topological chain (`1,1` versus
`x,x`), so those active observations are recorded but not treated as an
oracle.

The route now uses the same bounded quiescence loop as a cycle slot. A
combinational loop that does not quiesce remains a loud refusal.
