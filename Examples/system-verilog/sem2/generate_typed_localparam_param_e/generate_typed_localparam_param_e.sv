// IEEE 1800-2023 §§6.20.2, 27.4, 11.8.
module generate_typed_localparam_param_e #(parameter int W = 4)
    (input logic x, output logic y);
  if (W > 1) begin : g_hi
    localparam logic [W-1:0] BIAS = 'd1;
    assign y = x ^ BIAS[0];
  end else begin : g_lo
    localparam logic [W-1:0] BIAS = 'd0;
    assign y = x ^ BIAS[0];
  end
endmodule
