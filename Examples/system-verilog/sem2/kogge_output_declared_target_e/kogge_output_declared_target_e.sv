module kogge_output_declared_target_e #(parameter int WIDTH = 4)(input logic [WIDTH-1:0] a, output logic [WIDTH-1:0] o_sum);
  logic [WIDTH-1:0] stage;
  assign stage = a;
  assign o_sum[0] = stage[0];
  genvar i;
  generate for (i=1; i<WIDTH; i++) begin : g
    assign o_sum[i] = stage[i];
  end endgenerate
endmodule
