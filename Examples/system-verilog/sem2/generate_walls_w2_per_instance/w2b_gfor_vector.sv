// W2b: as W2a, with a packed vector per iteration.
module m #(parameter int unsigned N = 2) (
  input  logic [N-1:0] a,
  output logic [N-1:0] q
);
  for (genvar k = 0; k < N; k++) begin : g
    logic [1:0] t;
    assign t    = {a[k], ~a[k]};
    assign q[k] = t[0];
  end
endmodule
