// A procedural `for` loop with a blocking assignment in its body: each iteration reads what the previous one wrote.
module for_blocking #(parameter int N = 4) (input logic clk, input logic [7:0] d, output logic [7:0] q);
  logic [7:0] acc;
  always_ff @(posedge clk) begin
    acc = d;
    for (int i = 0; i < N; i++) acc = acc + 8'd1;
    q <= acc;
  end
endmodule
