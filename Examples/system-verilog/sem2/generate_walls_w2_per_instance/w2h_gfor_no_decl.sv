// W2h (control): the same loop with no declaration inside the loop.
module m #(parameter int unsigned N = 2) (
  input  logic [N-1:0] a,
  output logic [N-1:0] q
);
  for (genvar k = 0; k < N; k++) begin : g
    assign q[k] = ~a[k];
  end
endmodule
