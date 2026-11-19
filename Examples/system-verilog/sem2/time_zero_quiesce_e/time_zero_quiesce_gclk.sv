// IEEE 1800-2023 §4.7: a continuous driver and an edge process share time zero.
module time_zero_quiesce_gclk(input logic d, output logic q);
  logic g;
  assign g = 1'b1;
  always_ff @(posedge g) q <= d;
endmodule
