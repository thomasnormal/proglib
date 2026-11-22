// A `while` loop in an edge process.
module while_loop (input logic clk, input logic [7:0] d, output logic [7:0] q);
  logic [7:0] n;
  always_ff @(posedge clk) begin
    n = d;
    while (n[7]) n = n << 1;
    q <= n;
  end
endmodule
