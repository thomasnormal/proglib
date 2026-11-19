// IEEE 1800-2023 §§4.7 and 9.4.2: continuous driver and edge wait share time zero.
module event_assign_gclk(input logic d, output logic q);
  logic g;
  assign g = 1'b1;
  always_ff @(posedge g) q <= d;
endmodule
