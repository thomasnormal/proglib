module gen_localparam_leaf #(parameter int W = 1) (output logic [W-1:0] y);
  assign y = '0;
endmodule

module gen_localparam_child #(parameter int W = 2) (output logic [W:0] y);
  generate if (W > 0) begin : g
    localparam int CW = W + 1;
    gen_localparam_leaf #(.W(CW)) u(y);
  end endgenerate
endmodule

module gen_localparam_top #(parameter int W = 2) (output logic [W:0] y);
  gen_localparam_child #(.W(W)) c(y);
endmodule
