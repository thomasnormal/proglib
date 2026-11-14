// An indexed part select whose base is not affine (`i*i`): refused, naming the select.
module gen_part_sq #(parameter int N = 4) (
  input  logic [4*N-1:0] a,
  output logic [N-1:0]   y
);
  genvar i;
  generate
    for (i = 0; i < N; i++) begin : g_out
      assign y[i] = ^a[i*i +: 2];
    end
  endgenerate
endmodule
