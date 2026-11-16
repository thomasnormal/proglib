# Non-topological continuous-assignment wall

This source is the faithful public wall-2 repro for the canonical E settle
boundary. Its source order is deliberately non-topological (`a = b; b = x;
y = a`). Canonical E now repeats the continuous-assignment region until the
view is stable, as required by IEEE 1800-2023 §§4.5 and 10.3, with a bounded
loud refusal for a non-quiescing combinational loop.

Icarus Verilog 13.0, Xcelium 24.03-s004, and the E receipt all produce
`y=0,1,x,z` for the four source inputs. The ordinary census has no E
instantiation refusal for this fixture.
