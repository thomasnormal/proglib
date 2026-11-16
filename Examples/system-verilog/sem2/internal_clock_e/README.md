# Internal clock source wall

The source derives `generated_clock` from an input and clocks an edge process
from it. The ordinary `Design2`/run2 loader keeps the exact `Clock:source`
refusal because that view has one implicit top-level cycle edge. Canonical E is
the definition: direct `PDesign.instantiateE2` execution detects the generated
edge in the same slot and produces `result = x,1,1,1,0` for enable
0/1/x/z/1. This follows IEEE 1800-2023 §§4.4 and 9.4.2; hardware clock-gating
and metastability remain outside the model. Icarus Verilog 13.0 and Xcelium
24.03-s004 match these five rows.
