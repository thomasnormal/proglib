// Comma-separated ANSI port declarations (IEEE 1800-2023 §23.2.2.3): a later
// identifier in a list inherits the direction, port kind, data type and packed
// dimensions of the port before it.  Here a net list (`a, b`) and a variable
// list (`x, y`) both carry a parameter-dependent packed dimension, so the
// symbolic envelope must give `b` and `y` the same `[P+Q:0]` as `a` and `x`.
module ansi_port_inherit #(parameter integer P = 3, parameter integer Q = 4) (
    input  wire clk,
    input  wire [P+Q:0] a, b,
    output logic [P+Q:0] x, y
);
  assign x = a ^ b;
  always_ff @(posedge clk) y <= a + b;
endmodule
