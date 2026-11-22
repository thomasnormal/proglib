// IEEE 1800-2023 §§4.7 and 9.4.2: a clocked async-reset process has no time-zero activation.
module clocked_reset_guard_e(input logic clk, input logic rst_n, input logic d, output logic q);
always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n) q <= 1'b0;
  else q <= d;
end
endmodule
