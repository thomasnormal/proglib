// IEEE 1800-2023 §§10.3 and 11.5.1: an unknown bit index does not erase
// later continuous assignments in the same source-shaped design.
module arraybitsel_unknown_index_audit_e #(
    parameter int WIDTH = 1
) (
    input logic d,
    output logic q
);
  logic [3:0] mem [0:1];
  genvar i;
  generate for (i = 0; i < WIDTH; i++) begin : bits
    assign mem[0][(i ? 1'bx : i)] = d;
  end endgenerate
  genvar j;
  generate for (j = 0; j < 1; j++) begin : output_assign
    assign q = 1'b1;
  end endgenerate
endmodule
