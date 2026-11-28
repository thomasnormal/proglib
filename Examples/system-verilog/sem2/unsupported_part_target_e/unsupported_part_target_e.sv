module unsupported_part_target_e (input logic [15:0] d, output logic [31:0] o);
  logic [3:0][7:0] a;
  assign a[2:1] = d;
  assign a[3 -: 1] = d[7:0];
  assign o = a;
endmodule
