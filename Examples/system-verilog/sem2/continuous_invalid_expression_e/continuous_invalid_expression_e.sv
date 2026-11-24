module continuous_invalid_expression_e (input logic [3:0] a, input logic [3:0] b, output logic [3:0] y);
  typedef logic [3:0] word_t;
  word_t t;
  assign t = a + b;
  assign y = t;
endmodule
