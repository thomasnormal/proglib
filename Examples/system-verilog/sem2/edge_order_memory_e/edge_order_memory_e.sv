// Clean-room edge-order witness: one memory loop and two scalar NBA writers.
module edge_order_memory_e #(parameter int N = 4) (
  input logic clk,
  input logic rst,
  input logic [7:0] a_in,
  input logic [7:0] b_in,
  output logic [7:0] a_q,
  output logic [7:0] b_q,
  output logic [7:0] rd
);
  logic [7:0] mem [0:N-1];
  always_ff @(posedge clk) begin
    if (rst) begin
      for (int i = 0; i < N; i++) mem[i] <= '0;
    end
  end
  always_ff @(posedge clk) a_q <= a_in;
  always_ff @(posedge clk) b_q <= b_in;
  assign rd = mem[0];
endmodule
