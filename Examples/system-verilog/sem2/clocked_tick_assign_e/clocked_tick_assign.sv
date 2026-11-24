// Clean-room repro for the clocked-route topoC refusal.
// The derived tick is consumed by the same sequential process that advances
// the divider phase.  No memory, hierarchy, or parameter is involved.
module clocked_tick_assign (
  input  logic        clk,
  input  logic        rst_n,
  input  logic        ena,
  input  logic [23:0] divider_q,
  output logic [23:0] phase,
  output logic        tick_seen
);
  logic do_tick;

  assign do_tick = (divider_q == 24'd0) ||
                   ({1'b0, phase} + 25'd256 >= {1'b0, divider_q});

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      phase <= 24'd0;
      tick_seen <= 1'b0;
    end else begin
      tick_seen <= 1'b0;
      if (ena && do_tick) begin
        tick_seen <= 1'b1;
        phase <= phase + 24'd256 - divider_q;
      end else if (ena) begin
        phase <= phase + 24'd256;
      end
    end
  end
endmodule
