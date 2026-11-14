// One mutually exclusive generate branch drives an implicit output wire.
module net_generated_output_port_canonical_e #(parameter integer N = 1) (
    input logic clk,
    output wire z_out
);
  generate
    if (N) begin : g
      assign z_out = 1'b0;
    end
  endgenerate
endmodule
