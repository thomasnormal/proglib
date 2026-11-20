module plain_internal_edge_e(input logic clk, d, output logic g, q);
  always @(posedge clk) g <= d;
  always @(posedge g) q <= 1'b1;
endmodule
