// Generic child generate whose parameter is not supplied by its parent.
module generate_unbound_parameter_leaf #(parameter int SPAN = 4)(
  input logic x,
  output logic y
);
  if (SPAN > 0) assign y = x;
  else assign y = !x;
endmodule
module generate_unbound_parameter_top(input logic x, output logic y);
  generate_unbound_parameter_leaf u_leaf(.x(x), .y(y));
endmodule
