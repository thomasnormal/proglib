// IEEE 1800-2023 §§4.7 and 10.4.1: edge races through a select assign and always_comb driver.
module edge_driver_closure_race_refuse(input logic clk, input logic d, output logic b_assign, output logic b_comb);
  logic a_assign;
  logic [0:0] w_assign;
  assign w_assign[0] = a_assign;
  always_ff @(posedge clk) a_assign = d;
  always_ff @(posedge clk) b_assign <= w_assign[0];

  logic a_comb, w_comb;
  always_comb w_comb = a_comb;
  always_ff @(posedge clk) a_comb = d;
  always_ff @(posedge clk) b_comb <= w_comb;
endmodule
