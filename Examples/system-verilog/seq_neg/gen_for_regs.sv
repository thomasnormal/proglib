// Outside the clocked instantiation pass: a generate loop of registers (IEEE 1800-2017 27.4). The pass evaluates a
// conditional generate; it does not expand a loop.
module gen_for_regs #(parameter int W = 4) (input logic clk, input logic [W-1:0] d, output logic [W-1:0] q);
  generate for (genvar i = 0; i < W; i++) begin : g
    always_ff @(posedge clk) q[i] <= d[W-1-i];
  end endgenerate
endmodule
