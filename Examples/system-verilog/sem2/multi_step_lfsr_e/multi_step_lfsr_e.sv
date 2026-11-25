module multi_step_lfsr_e #(parameter int WIDTH = 8, parameter logic [WIDTH-1:0] TAPS = '0) (
  input logic clk, input logic rstn, input logic en, output logic [WIDTH-1:0] state);
  logic [WIDTH-1:0] s [0:8];
  assign s[0] = state;
  for (genvar i = 0; i < 8; i++) begin : step
    assign s[i+1] = s[i][0] ? ((s[i] >> 1) ^ TAPS) : (s[i] >> 1);
  end
  always_ff @(posedge clk or negedge rstn)
    if (!rstn) state <= 'd1; else if (en) state <= s[8];
endmodule
