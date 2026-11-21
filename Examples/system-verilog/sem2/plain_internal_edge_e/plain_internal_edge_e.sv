module plain_internal_edge_e(input logic clk, d, e, output logic g, q);
  always @(posedge clk) g <= d;
  always @(posedge g) q <= e;
endmodule
