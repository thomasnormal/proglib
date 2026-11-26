// loopfuel-audit5: 4.7: refuse
module a5_ext_gen_long (input logic clk, output logic [31:0] q, output logic [31:0] r);
  integer i;
  if (1) begin : g
    always @(posedge clk) begin
      q = 0;
      for (i = 0; i < 5000; i = i + 1) q = q + 1;
    end
    always @(posedge clk) begin
      r = 0;
      for (i = 0; i < 3000; i = i + 1) r = r + 1;
    end
  end
endmodule
