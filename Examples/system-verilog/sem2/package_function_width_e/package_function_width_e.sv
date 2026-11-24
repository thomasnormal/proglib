package package_function_width_e_pkg;
  function automatic integer vbits(input integer value);
    integer result;
    begin
      result = 0;
      case (value)
        1: result = 1;
        default: result = $clog2(value);
      endcase
      vbits = result;
    end
  endfunction
endpackage

module package_function_width_e #(parameter int unsigned N = 1)
    (output logic [package_function_width_e_pkg::vbits(N)-1:0] y);
  assign y = '0;
endmodule
