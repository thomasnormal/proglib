module generated_instance_timeout_e_child(input logic d, output logic q, input logic clk, input logic rstn);
  always_ff @(posedge clk or negedge rstn)
    if (!rstn) q <= 1'b0;
    else q <= d;
endmodule

module generated_instance_timeout_e #(parameter int WIDTH = 1)
    (input logic [WIDTH-1:0] d, output logic [WIDTH-1:0] q,
     input logic clk, input logic rstn);
  logic [WIDTH-1:0] mid;
  generate for (genvar k = 0; k < WIDTH; k++) begin : lanes
    generated_instance_timeout_e_child first
      (.d(d[k]), .q(mid[k]), .clk(clk), .rstn(rstn));
    generated_instance_timeout_e_child second
      (.d(mid[k]), .q(q[k]), .clk(clk), .rstn(rstn));
  end endgenerate
endmodule
