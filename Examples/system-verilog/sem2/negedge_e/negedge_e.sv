// Canonical E B1: negative-edge clock, IEEE 1800-2023 §9.4.2.
module negedge_e (
  input logic clk,
  input logic d,
  output logic q
);
  always_ff @(negedge clk) q <= d;
endmodule
