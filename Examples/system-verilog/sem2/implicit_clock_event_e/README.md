# Implicit event-control refusal

The source uses `always_ff @(clk)` without an edge keyword. Slang retains the
parser-shaped any-edge process under IEEE 1800-2023 §9.4.2, and ordinary E
retains the design before its explicit `Clock:implicit` execution refusal.
The clocked `sv_structure` profile has the same any-edge boundary. The eight
source rows are pinned against Icarus Verilog 13.0 and Xcelium 24.03-s004.
