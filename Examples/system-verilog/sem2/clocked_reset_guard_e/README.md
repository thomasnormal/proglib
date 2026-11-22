# Clocked asynchronous-reset guard

This clean-room source isolates a one-register `always_ff @(posedge clk or
negedge rst_n)` process. Canonical E must not run the `always_comb` self-read
admission analysis or the time-zero activation scan as if the edge process
were a reactive writer. The source-shaped guard now instantiates without a
heartbeat timeout under IEEE 1800-2023 §§4.7 and 9.4.2.

`agree.lean` checks canonical-E admission and eight four-state rows. The
receipt compares the unchanged source against Icarus Verilog 13.0 and Xcelium
24.03-s004.
