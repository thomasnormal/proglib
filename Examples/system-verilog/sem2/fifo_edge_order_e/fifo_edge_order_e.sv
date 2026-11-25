// Circular-buffer FIFO clean-room shape for the memory edge-order wall.
module fifo_edge_order_e #(
  parameter int DATA_W = 8,
  parameter int DEPTH = 4
) (
  input logic clk,
  input logic rst,
  input logic push,
  input logic pop,
  input logic [DATA_W-1:0] din,
  output logic [DATA_W-1:0] dout,
  output logic [DATA_W:0] count
);
  logic [DATA_W-1:0] mem [0:DEPTH-1];
  logic [$clog2(DEPTH)-1:0] rd_ptr;
  logic [$clog2(DEPTH)-1:0] wr_ptr;

  assign dout = mem[rd_ptr];

  always_ff @(posedge clk) begin
    if (rst) begin
      rd_ptr <= '0;
      count <= '0;
    end else begin
      if (pop && (count != 0))
        rd_ptr <= rd_ptr + 1'b1;
      if (push && (count != DEPTH) && !(pop && (count != 0)))
        count <= count + 1'b1;
      else if (pop && (count != 0))
        count <= count - 1'b1;
    end
  end

  always_ff @(posedge clk) begin
    if (rst) begin
      wr_ptr <= '0;
      for (int i = 0; i < DEPTH; i++)
        mem[i] <= '0;
    end else if (push && (count != DEPTH)) begin
      mem[wr_ptr] <= din;
      wr_ptr <= wr_ptr + 1'b1;
    end
  end
endmodule
