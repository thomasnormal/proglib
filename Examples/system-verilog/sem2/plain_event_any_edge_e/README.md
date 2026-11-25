# Plain event-control boundary

`always_ff @(clk)` is retained as a parser-native any-edge process under
IEEE 1800-2023 §9.4.2. The ordinary executor admits and runs the source-shaped
process. The clocked `sv_structure` profile explicitly refuses it because the
profile covers edge events only.

This is the clean-room `plain_event_any_edge` shape. The ordinary route's
four rows match both pinned simulators, while `sv_structure` keeps the
explicit any-edge refusal.
