// Clean-room positive row: an unsigned complete package-array member.
package unsigned_member_pkg;
  typedef struct packed { logic [7:0] v; } elem_t;
  localparam elem_t P [2] = '{'{v: 8'd3}, '{v: 8'd5}};
endpackage
module package_unsigned_member_canonical_e #(parameter int K = 1) (
  input logic [7:0] i,
  output logic [31:0] o
);
  function automatic int f();
    int s;
    s = 0;
    for (int k = K; k < K + 1; k++) s = s + 32'(unsigned_member_pkg::P[k].v);
    return s;
  endfunction
  localparam int R = f();
  assign o = R + i;
endmodule
