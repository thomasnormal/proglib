// the same at N = 3: inner leaves i = 2, the outer step makes it 3 >= N, so one outer trip in SV: c = 2
module lf3_ext_nest_p3 #(parameter int N = 3) (input logic clk, output logic [31:0] q);
  logic [31:0] c; integer i;
  always_ff @(posedge clk) begin
    c = 32'd0;
    for (i = 0; i < N; i = i + 1) for (i = 0; i < 2; i = i + 1) c = c + 32'd1;
    q <= c;
  end
endmodule
