package signed_struct_elem_pkg;
  typedef struct packed signed { logic [7:0] v; } elem_t;
  localparam elem_t P [2] = '{'{v: 8'hFD}, '{v: 8'h05}};
endpackage
module package_signed_struct_elem_e (input logic [7:0] i, output logic [31:0] o);
  function automatic int f();
    int s;
    s = 0;
    for (int k = 0; k < 2; k++) s = s * 1000 + 32'(signed_struct_elem_pkg::P[k]);
    return s;
  endfunction
  localparam int R = f();
  assign o = R + i;
endmodule
