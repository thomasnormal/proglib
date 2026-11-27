// d01 shape; the testbench applies the first row at time 0 with clk=1 (x->1 edge),
// while always_comb runs its time-zero activation (9.2.2.2.2).
module time_zero_input_comb_e(input logic clk, input logic en, input logic [1:0] a, b,
                     output logic [1:0] q);
  logic [1:0] nxt;
  always_comb begin
    nxt = a;
    if (en) nxt = b;
  end
  always_ff @(posedge clk) q <= nxt;
endmodule
