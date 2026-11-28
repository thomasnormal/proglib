module w11_mod (input logic clk, input logic en, input logic a, b, output logic q);
  logic nxt;
  always_comb begin
    nxt = a;
    if (en) nxt = b;
  end
  always_ff @(posedge clk) q <= nxt;
endmodule
