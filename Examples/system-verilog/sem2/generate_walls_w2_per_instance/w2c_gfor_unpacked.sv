// W2c: as W2a, with an unpacked array per iteration.
module m #(parameter int unsigned N = 2) (
  input  logic [N-1:0] a,
  output logic [N-1:0] q
);
  for (genvar k = 0; k < N; k++) begin : g
    logic t [0:1];
    assign t[0] = a[k];
    assign t[1] = ~a[k];
    assign q[k] = t[1];
  end
endmodule
