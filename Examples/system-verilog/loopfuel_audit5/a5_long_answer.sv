module a5_long_answer (input logic clk, output logic [31:0] q);
  logic [31:0] c;
  always_ff @(posedge clk) begin
    c = 32'd0;
    for (int i = 0; i < 5001; i++) c = c + 32'd1;
    q <= c;
  end
endmodule
