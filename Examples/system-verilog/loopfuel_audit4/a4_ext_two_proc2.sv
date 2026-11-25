module a4_ext_two_proc2 (input logic clk, output logic [31:0] q, r);
  integer i;
  always @(posedge clk) begin
    q = 0;
    for (i = 0; i < 4; i = i + 1) q = q + 1;
  end
  always @(posedge clk) begin
    r = 0;
    for (i = 0; i < 3; i = i + 1) r = r + 1;
  end
endmodule
