# Logic-typed localparam boundary receipt

The source retains a logic-typed localparam under IEEE 1800-2023 §6.20.2.
Canonical functional rows match both pinned simulators. The clocked
`sv_structure` profile continues to refuse this localparam type explicitly.

This is the clean-room `blk_localparam_logic_type` wall. The ordinary
functional receipt remains separate from the clocked-profile refusal.

The current receipt reports four matching source rows on Icarus Verilog 13.0
and Xcelium 24.03-s004.
