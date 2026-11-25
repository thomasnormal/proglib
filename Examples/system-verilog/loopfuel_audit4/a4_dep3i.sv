// 3*(0+1+..+7) = 84
module a4_dep3i #(parameter int N = 8) (input logic clk, output logic [31:0] q);
  logic [31:0] c;
  always_ff @(posedge clk) begin
    c = 32'd0;
    for (int i = 0; i < N; i++) for (int j = 0; j < 3 * i; j++) c = c + 32'd1;
    q <= c;
  end
endmodule
