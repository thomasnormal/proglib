// Same-edge blocking race with the source order reversed. IEEE 1800-2023
// §4.7 leaves the active-region process order open.
module edge_blocking_race_refuse2(input logic clk, d, output logic a, b);
  always_ff @(posedge clk) b = a;
  always_ff @(posedge clk) a = d;
endmodule
