module leaf_indexed #(parameter integer W = 4)(input wire [W-1:0] a, output wire [W-1:0] y);
  assign y = a;
endmodule
module hierarchy_indexed_canonical_e #(parameter integer W = 8)(input wire [W-1:0] a, output wire [W-1:0] y);
  leaf_indexed #(.W(W/2)) lo(.a(a[0 +: W/2]), .y(y[0 +: W/2]));
  leaf_indexed #(.W(W/2)) hi(.a(a[W/2 +: W/2]), .y(y[W/2 +: W/2]));
endmodule
