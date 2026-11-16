// A word split at a parameter: the low `P` bits through one parameterized identity leaf, the high `W - P` bits through
// another, the parent's output a `wire` tiled by the two instances' output ports. Two parameters at the parent.
module split_leaf #(parameter integer W = 4) (input wire [W-1:0] a, output wire [W-1:0] y);
  assign y = a;
endmodule
module split_word #(parameter integer W = 8, parameter integer P = 3) (input wire [W-1:0] a, output wire [W-1:0] y);
  split_leaf #(.W(P)) lo(.a(a[P-1:0]), .y(y[P-1:0]));
  split_leaf #(.W(W - P)) hi(.a(a[W-1:P]), .y(y[W-1:P]));
endmodule
