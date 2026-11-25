// 4'(12) is signed 4'b1100 = -4: i = -4..2, 7 trips in SV
module a4_sz_init (input logic clk, output logic [31:0] q);
  logic [31:0] c;
  always_ff @(posedge clk) begin
    c = 32'd0;
    for (int i = 4'(12); i < 3; i++) c = c + 32'd1;
    q <= c;
  end
endmodule
