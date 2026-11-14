// `$clog2` of a quotient by a parameter: a localparam divides by an integer literal only.
module gen_clog2q_div #(parameter int N = 11, parameter int D = 8) (
  input  logic [N-1:0] a,
  output logic [N-1:0] q
);
  localparam integer NI = $clog2((N + 9) / D) + 1;
  assign q = a;
endmodule
