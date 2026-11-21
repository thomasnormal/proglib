module duplicate_active_scope_e #(parameter int N=2)
  (input logic [N-1:0] x, output logic [N-1:0] y);
  generate
    if (N > 0) begin : first
      logic value;
      assign value = x[0];
      assign y[0] = value;
    end
    if (N > 1) begin : second
      logic value;
      assign value = x[1];
      assign y[1] = value;
    end
  endgenerate
endmodule
