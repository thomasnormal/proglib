module untyped_child_override_leaf #(parameter P = 0) (output logic [7:0] y);
  assign y = P;
endmodule

module untyped_child_override_top (output logic [7:0] y);
  untyped_child_override_leaf #(.P(8'hff)) u(y);
endmodule
