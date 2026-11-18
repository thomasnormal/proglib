// Outside the clocked profile: a flip-flop on 2-state data (`bit`); the clocked views are 4-state.
module two_state_reg(input logic clk, input bit d, output bit q);
  always_ff @(posedge clk) q <= d;
endmodule
