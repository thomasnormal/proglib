// IEEE 1800-2023 §12.7: a parameter-bound procedural loop remains source-shaped.
module clocked_param_loop_e #(parameter int WIDTH = 4, parameter int DEPTH = 3)
  (input logic clk, input logic [WIDTH-1:0] d, output logic [WIDTH-1:0] q);
  logic [WIDTH-1:0] mem [0:DEPTH-1];
  integer i;
  always_ff @(posedge clk) begin
    for (i = DEPTH-1; i > 0; i = i - 1) mem[i] <= mem[i-1];
    mem[0] <= d;
  end
  assign q = mem[DEPTH-1];
endmodule
