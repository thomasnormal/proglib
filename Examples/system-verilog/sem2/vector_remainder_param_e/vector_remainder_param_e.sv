module vector_remainder_param_e #(parameter integer N = 13)
    (output logic [7:0] y);
  localparam logic [7:0] R = N % 8'd5;
  assign y = R;
endmodule
