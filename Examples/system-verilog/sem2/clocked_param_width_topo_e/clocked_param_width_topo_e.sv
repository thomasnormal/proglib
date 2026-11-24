module clocked_param_width_topo_e #(parameter int D = 8, parameter int AW = 3) (
  input logic clk, input logic rstn, input logic en, output logic full
);
  logic [AW:0] cnt, cnt_nxt;
  assign full = (cnt == D);
  assign cnt_nxt = en ? cnt + 1'b1 : cnt;
  always_ff @(posedge clk or negedge rstn)
    if (!rstn) cnt <= '0; else cnt <= cnt_nxt;
endmodule
