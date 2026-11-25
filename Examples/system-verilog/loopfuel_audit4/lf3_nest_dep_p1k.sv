// 0 + 1000 + 2000 = 3000
module lf3_nest_dep_p1k #(parameter int N = 3) (input logic clk, output logic [31:0] q);
  logic [31:0] c;
  always_ff @(posedge clk) begin
    c = 32'd0;
    for (int i = 0; i < N; i++) for (int j = 0; j < 1000 * i; j++) c = c + 32'd1;
    q <= c;
  end
endmodule
