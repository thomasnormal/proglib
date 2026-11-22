// The shift register of shift_for.sv with a plain `always`, a module-level loop variable and the step `i = i + 1`.
module shift_v2001 #(parameter int W = 8, parameter int N = 4)
  (input logic clk, input logic [W-1:0] d, output logic [W-1:0] q);
  logic [W-1:0] pipe [0:N-1];
  integer i;
  always @(posedge clk) begin
    pipe[0] <= d;
    for (i = 1; i < N; i = i + 1) pipe[i] <= pipe[i-1];
  end
  assign q = pipe[N-1];
endmodule
