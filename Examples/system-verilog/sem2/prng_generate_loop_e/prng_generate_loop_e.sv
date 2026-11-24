module prng_generate_loop_e_leaf(input logic clk, input logic rstn,
  input logic d, output logic q);
  always_ff @(posedge clk or negedge rstn)
    if (!rstn) q <= 1'b0;
    else q <= d;
endmodule

module prng_generate_loop_e #(parameter int N = 3)
  (input logic clk, input logic rstn,
   input logic [N-1:0] d, output logic [N-1:0] q);
  generate for (genvar k = 0; k < N; k++) begin : lanes
    prng_generate_loop_e_leaf u
      (.clk(clk), .rstn(rstn), .d(d[k]), .q(q[k]));
  end endgenerate
endmodule
