// Clean-room loader boundary for a mixed negative-edge clock and reset event list.
module loader_refuse_negedge_reset(input logic clk, rst_n, d, output logic q);
  always_ff @(negedge clk or negedge rst_n) begin
    if (!rst_n) q <= 1'b0;
    else q <= d;
  end
endmodule
