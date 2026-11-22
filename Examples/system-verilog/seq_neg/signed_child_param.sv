module signed_child #(parameter logic signed [3:0] P = 0)
  (output logic [63:0] value);
  assign value = P;
endmodule

module signed_parent #(parameter logic signed [3:0] P = -8)
  (output logic [63:0] value);
  signed_child #(.P(P)) child(.value(value));
endmodule
