package vector_remainder_param_e_pkg;
  function automatic integer ceil_div(input integer a, input integer b);
    return ((a % b) != 0) ? (a / b) + 1 : (a / b);
  endfunction
endpackage

module vector_remainder_param_e #(parameter integer N = 13)
    (output logic [7:0] y);
  localparam logic [7:0] R = vector_remainder_param_e_pkg::ceil_div(N, 5);
  assign y = R;
endmodule
