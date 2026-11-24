module module_integer_for_e #(parameter int N = 2) (
  input logic clk, input logic en, input logic [N-1:0] d,
  output logic [N-1:0] q);
  integer i;
  always_ff @(posedge clk) begin
    if (en) for (i = 0; i < N; i = i + 1) q[i] <= d[i];
  end
endmodule
