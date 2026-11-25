// Source-shaped generated unpacked shift-register storage, IEEE 1800-2023 §§7.4 and 27.4.
module generated_unpacked_fifo_e #(parameter int D = 2, W = 8) (
  input logic clk,
  input logic en,
  input logic [W-1:0] d,
  output logic [W-1:0] q
);
  logic [W-1:0] mem [D];
  for (genvar k = 0; k < D; k++) begin : g_mem
    always_ff @(posedge clk) if (en) mem[k] <= d;
  end
  assign q = mem[0];
endmodule
