// The same drivers in a different source order must settle identically.
module time_zero_quiesce_gclk2(input logic d, output logic q);
  logic g, b;
  assign g = b;
  assign b = 1'b1;
  always_ff @(posedge g) q <= d;
endmodule
