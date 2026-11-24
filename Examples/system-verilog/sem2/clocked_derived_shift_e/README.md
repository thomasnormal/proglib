# Clocked derived-assignment route

This clean-room source has three scalar continuous assignments in a derived
chain. The asynchronous-reset edge process consumes the final derived value.
The ordinary E clocked structure route admits the unchanged source and proves
the topological and edge-order obligations. The differential receipt covers
reset, load, shift, masks, and the first x/z samples against Icarus Verilog
13.0 and Xcelium 24.03-s004.
