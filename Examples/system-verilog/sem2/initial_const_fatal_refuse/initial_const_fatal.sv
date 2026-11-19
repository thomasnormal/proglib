module initial_const_fatal #(parameter integer N=1) (input logic clk, input logic d, output logic q);
initial begin
  if (N < 1) $fatal(1, "parameter must be positive");
end
always @(posedge clk) q <= d;
endmodule
