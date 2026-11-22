// A shift register over an unpacked array, shifted by a procedural `for` loop of nonblocking assignments.
module shift_for #(parameter int W = 8, parameter int N = 4)
  (input logic clk, input logic [W-1:0] d, output logic [W-1:0] q);
  logic [W-1:0] pipe [0:N-1];
  always_ff @(posedge clk) begin
    pipe[0] <= d;
    for (int i = 1; i < N; i++) pipe[i] <= pipe[i-1];
  end
  assign q = pipe[N-1];
endmodule
