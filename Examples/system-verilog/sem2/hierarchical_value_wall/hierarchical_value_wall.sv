module hierarchy_leaf(output logic internal_value);
  assign internal_value = 1'b1;
endmodule
module hierarchical_value_repro(output logic result);
  hierarchy_leaf u();
  assign result = u.internal_value;
endmodule
