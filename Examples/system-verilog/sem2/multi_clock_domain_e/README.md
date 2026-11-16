# Multiple input clocks

The source has independent `posedge aclk` and `posedge bclk` processes. The
ordinary one-clock `run2` view keeps its exact `Clock:multiple` refusal.
Canonical E's source-shaped step accepts both input clocks as ordinary inputs;
separate, coincident, stopped, x, and z transitions are all rows in the receipt
under IEEE 1800-2023 §§4.4 and 9.4.2. Icarus Verilog 13.0, Xcelium
24.03-s004, and direct E agree on the eight rows inherited from the simulator
receipt.
