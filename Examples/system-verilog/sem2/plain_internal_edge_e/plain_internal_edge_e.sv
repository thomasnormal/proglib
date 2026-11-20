module plain_internal_edge_e(input logic clk, input logic d,
    output logic g_plain, q_plain, g_ff, q_ff);
  always @(posedge clk) g_plain <= d;
  always @(posedge g_plain) q_plain <= 1'b1;
  always_ff @(posedge clk) g_ff <= d;
  always_ff @(posedge g_ff) q_ff <= 1'b1;
endmodule
