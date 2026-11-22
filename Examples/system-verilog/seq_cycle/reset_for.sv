// A memory cleared by a procedural `for` loop under a synchronous reset, written at a run-time address otherwise.
module reset_for #(parameter int W = 8, parameter int N = 4)
  (input logic clk, input logic rst, input logic we, input logic [4:0] wa, input logic [W-1:0] wd,
   input logic [4:0] ra, output logic [W-1:0] rd);
  logic [W-1:0] mem [0:N-1];
  always_ff @(posedge clk) begin
    if (rst) begin
      for (int i = 0; i < N; i++) mem[i] <= '0;
    end else if (we) mem[wa] <= wd;
  end
  assign rd = mem[ra];
endmodule
