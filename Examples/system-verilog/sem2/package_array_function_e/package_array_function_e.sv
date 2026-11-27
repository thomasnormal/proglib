package tab;
  localparam int unsigned ROM [0:3] = '{32'd3, 32'd5, 32'd7, 32'd11};
endpackage
module package_array_function_e (input logic [7:0] i, output logic [7:0] o);
  function automatic int unsigned last(input int unsigned n);
    return tab::ROM[n];
  endfunction
  localparam int unsigned K = last(2);
  assign o = i + K[7:0];
endmodule
