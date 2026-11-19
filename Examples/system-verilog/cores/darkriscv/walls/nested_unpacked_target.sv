// Clean-room receipt for a generated two-rank procedural target.
module nested_unpacked_target #(
  parameter int W = 8,
  parameter int R = 2,
  parameter int C = 2
) (
  input logic clk,
  input logic rst_n,
  input logic [W-1:0] d,
  output logic [W-1:0] q
);
  logic [W-1:0] weights [0:R-1][0:C-1];
  genvar row, col;
  generate
    for (row = 0; row < R; row = row + 1) begin : rows
      for (col = 0; col < C; col = col + 1) begin : cols
        always_ff @(posedge clk or negedge rst_n) begin
          if (!rst_n)
            weights[row][col] <= '0;
          else
            weights[row][col] <= d;
        end
      end
    end
  endgenerate
  assign q = weights[0][0];
endmodule
