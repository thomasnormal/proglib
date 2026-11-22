// A procedural `for` loop whose header steps by two: every other element is cleared.
module for_step2 #(parameter int N = 8) (input logic clk, input logic rst, output logic [7:0] q);
  logic [7:0] mem [0:N-1];
  always_ff @(posedge clk) begin
    if (rst) for (int i = 0; i < N; i += 2) mem[i] <= 8'd0;
  end
  assign q = mem[0];
endmodule
