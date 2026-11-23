module unpacked_bitselect_target #(parameter int W = 4) (
  input logic [W-1:0] a, b,
  output logic [W-1:0] y
);
  localparam int S = $clog2(W);
  logic [W-1:0] t [0:S];
  genvar i;
  for (i = 0; i < W; i++) begin : g
    assign t[0][i] = a[i] ^ b[i];
    assign y[i] = t[0][i];
  end
endmodule
