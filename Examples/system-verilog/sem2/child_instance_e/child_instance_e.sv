// Generic nested hierarchy repro with a generated two-stage scan-capable child.
module scan_leaf(input logic d, output logic q, input logic clk, input logic rst_n,
    input logic se, input logic si);
  always_ff @(posedge clk or negedge rst_n)
    if (!rst_n) q <= 1'b0; else q <= d;
endmodule
module scan_chain #(parameter int W=1)(input logic [W-1:0] d,
    output logic [W-1:0] q, input logic clk, input logic rst_n,
    input logic se, input logic si);
  logic [W-1:0] mid;
  generate for (genvar i=0; i<W; i++) begin : stages
    scan_leaf first (.d(d[i]), .q(mid[i]), .clk(clk), .rst_n(rst_n), .se(se), .si());
    scan_leaf second (.d(mid[i]), .q(q[i]), .clk(clk), .rst_n(rst_n), .se(se), .si());
  end endgenerate
endmodule
module child_instance_scan(input logic clk, input logic rst_n, input logic d, output logic q);
  scan_chain u_chain(.d(d), .q(q), .clk(clk), .rst_n(rst_n), .se(1'b0), .si());
endmodule
