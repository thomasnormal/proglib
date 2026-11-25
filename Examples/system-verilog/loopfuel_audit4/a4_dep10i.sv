// 10*(0+1+2+3) = 60
module a4_dep10i #(parameter int N = 4) (input logic clk, output logic [31:0] q);
  logic [31:0] c;
  always_ff @(posedge clk) begin
    c = 32'd0;
    for (int i = 0; i < N; i++) for (int j = 0; j < 10 * i; j++) c = c + 32'd1;
    q <= c;
  end
endmodule
