// Generic typed unpacked-net witness for the NetSymbol:type boundary.
module typed_unpacked_net(
  input logic [7:0] x,
  output logic [7:0] y
);
  wire [7:0] tree [0:3];
  assign tree[0] = x;
  assign tree[1] = tree[0];
  assign tree[2] = tree[1];
  assign tree[3] = tree[2];
  assign y = tree[0];
endmodule
