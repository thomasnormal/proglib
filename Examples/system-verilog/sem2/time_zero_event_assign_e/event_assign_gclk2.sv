// Assignment order leaves the same time-zero race in a different source order.
module event_assign_gclk2(input logic d, output logic q);
  logic g, b;
  assign g = b;
  assign b = 1'b1;
  always_ff @(posedge g) q <= d;
endmodule
