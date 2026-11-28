module signed_packed_array_target_e (input logic signed [3:0] s4, input logic [3:0] u4,
                output logic [15:0] o, output logic [23:0] p);
  logic signed [1:0][7:0] a;
  logic [2:0][7:0] b;
  assign a[0] = 4'sb1101;
  assign a[1] = s4;
  assign b[0] = u4;
  assign b[1] = {u4, u4, u4, u4};
  assign b[2] = s4 + 4'sd1;
  assign o = a;
  assign p = b;
endmodule
