// A register that zero-extends its data, with parameters of an unsigned type: the dimensions `[W-1:0]` and
// `[W+G-1:0]` are sized constant expressions over `int unsigned` (IEEE 1800-2017 11.6), not INT-class ones.
module unsigned_ext #(parameter int unsigned W = 4, parameter int unsigned G = 2)
  (input logic clk, input logic en, input logic [W-1:0] d, output logic [W+G-1:0] q);
  always_ff @(posedge clk) if (en) q <= d;
endmodule
