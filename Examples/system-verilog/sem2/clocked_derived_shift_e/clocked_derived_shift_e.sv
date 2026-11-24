// Clean-room receipt for a derived continuous-assignment dependency in the
// clocked route. The edge process consumes a scalar chain whose drivers are
// retained as source-shaped assignments.
module clocked_derived_shift_e #(parameter int N = 4) (
  input logic clk,
  input logic rst_n,
  input logic load,
  input logic [N-1:0] d,
  input logic [N-1:0] mask,
  output logic [N-1:0] q,
  output logic [N-1:0] observed
);
  logic [N-1:0] shifted;
  logic [N-1:0] selected;

  assign shifted = q << 1;
  assign selected = shifted | mask;
  assign observed = selected;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n)
      q <= '0;
    else if (load)
      q <= selected ^ d;
    else
      q <= shifted;
  end
endmodule
