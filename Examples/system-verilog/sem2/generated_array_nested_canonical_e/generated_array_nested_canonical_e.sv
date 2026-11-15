module generated_array_nested_canonical_e #(
  parameter int W = 8
) (
  input logic [W-1:0] x,
  input logic [W-1:0] taps,
  output logic [7:0] y
);
  logic [W-1:0] state [0:8];
  logic feedback [0:7];
  assign state[0] = x;
  genvar i;
  generate
    for (i = 0; i < 8; i = i + 1) begin : step
      assign feedback[i] = state[i][0];
      assign state[i+1] = feedback[i] ? ((state[i] >> 1) ^ taps)
                                      : (state[i] >> 1);
      assign y[i] = feedback[i];
    end
  endgenerate
endmodule
