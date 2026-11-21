module ff_internal_edge_e(input logic clk, d, e, output logic g, q);
  always_ff @(posedge clk) g <= d;
  always_ff @(posedge g) q <= e;
endmodule
