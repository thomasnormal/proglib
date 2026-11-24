package package_function_width_e_pkg;
  function automatic integer vbits(input integer value);
    return (value == 1) ? 1 : $clog2(value);
  endfunction
endpackage

module package_function_width_e #(parameter int unsigned N = 1)
    (output logic [package_function_width_e_pkg::vbits(N)-1:0] y);
  assign y = '0;
endmodule
