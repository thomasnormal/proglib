// Clean-room finite-state machine witness for the admitted NBA scheduler class.
module fsm_logic_confluence_e (
  input logic clk, rst, go,
  output logic busy, done
);
  logic [1:0] state;
  always_ff @(posedge clk) begin
    if (rst) state <= 2'd0;
    else case (state)
      2'd0: if (go) state <= 2'd1;
      2'd1: state <= 2'd2;
      2'd2: state <= 2'd0;
      default: state <= 2'd0;
    endcase
  end

  assign busy = (state == 2'd1);
  assign done = (state == 2'd2);
endmodule
