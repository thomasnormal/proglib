# Input edge at time zero beside always_comb

The first environment row drives `clk` from x to 1 while the mandatory
`always_comb` startup activation is pending. IEEE 1800-2023 §§4.7 and
9.2.2.2.2 leave that active-region ordering open, so canonical E refuses the
source-shaped design with `Event:time-zero`.

Icarus Verilog 13.0 produces `10`, `10`, `10`. Xcelium Verilog 24.03-s004
reports its startup result separately because this row is a known simulator
startup divergence.
