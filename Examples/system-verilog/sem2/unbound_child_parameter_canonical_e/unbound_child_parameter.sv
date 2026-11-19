// Generic child instance whose width parameter is not bound by the parent.
module unbound_child_parameter_leaf #(parameter int A_WIDTH = 8)(
  input logic [A_WIDTH-1:0] a,
  output logic [A_WIDTH-1:0] y
);
  assign y = a;
endmodule
module unbound_child_parameter_top(
  input logic [7:0] x,
  output logic [7:0] y
);
  unbound_child_parameter_leaf u_leaf(.a(x), .y(y));
endmodule
