// IEEE 1800-2023 §§4.7 and 10.4.1: a blocking write races with an edge reader through an assign.
module edge_assign_race_refuse(input logic clk, input logic d, output logic b);
  logic a, w;
  assign w = a;
  always_ff @(posedge clk) a = d;
  always_ff @(posedge clk) b <= w;
endmodule
