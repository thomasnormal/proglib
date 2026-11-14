// A shift of a parameter in a declared bound: the declarations stay atom-free (name the value with a localparam).
module gen_pow_decl #(parameter int N = 4) (
  input  logic [N-1:0] a,
  output logic [N-1:0] y
);
  logic [(1 << N) - 1:0] w;
  assign w = '0;
  assign y = a;
endmodule
