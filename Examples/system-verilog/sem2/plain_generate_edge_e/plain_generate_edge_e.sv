// R14 clean-room receipt: parser-native plain always processes inside a
// generate-for loop retain and substitute each genvar reference.
module plain_generate_edge_e #(parameter int W = 2) (
  input logic clk,
  input logic [W-1:0] d,
  output logic [W-1:0] q
);
  genvar i;
  generate
    for (i = 0; i < W; i = i + 1) begin : lane
      always @(posedge clk) q[i] <= d[W-1-i];
    end
  endgenerate
endmodule
