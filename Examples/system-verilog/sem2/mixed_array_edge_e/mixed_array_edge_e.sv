module mixed_array_edge_e (input logic clk, input logic [7:0] d, output logic [15:0] o);
  logic [1:0][7:0] a;
  assign a[0] = d;
  always_ff @(posedge clk) a[1] <= a[0] + 8'd1;
  assign o = a;
endmodule
