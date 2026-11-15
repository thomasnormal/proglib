// A generated full-width output-wire driver with a live RHS.
module net_generated_dynamic_output_port_canonical_e #(parameter integer N = 1) (
    input logic a,
    input logic b,
    output wire wready_o
);
  generate
    if (N) begin : g
      assign wready_o = ~a & ~b;
    end
  endgenerate
endmodule
