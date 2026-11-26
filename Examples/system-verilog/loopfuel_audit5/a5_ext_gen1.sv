// loopfuel-audit5: 4.7: either process may be suspended mid-loop: refuse
module a5_ext_gen1 (input logic clk, output logic [31:0] q, output logic [31:0] r);
  integer i;
  always @(posedge clk) begin
    q = 0;
    for (i = 0; i < 4; i = i + 1) q = q + 1;
  end
  if (1) begin : g
    always @(posedge clk) begin
      r = 0;
      for (i = 0; i < 3; i = i + 1) r = r + 1;
    end
  end
endmodule
