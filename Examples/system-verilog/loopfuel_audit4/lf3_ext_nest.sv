// nested loops share one external iterator: the inner loop resets i, so the outer loop never ends in SV
module lf3_ext_nest (input logic clk, output logic [31:0] q);
  logic [31:0] c; integer i;
  always_ff @(posedge clk) begin
    c = 32'd0;
    for (i = 0; i < 4; i = i + 1) for (i = 0; i < 2; i = i + 1) c = c + 32'd1;
    q <= c;
  end
endmodule
