module vector_slice_child_e_lane #(parameter int WIDTH = 8)
 (input logic [WIDTH-1:0] a, output logic [2*WIDTH-1:0] y);
 assign y = {WIDTH'(0), a};
endmodule

module vector_slice_child_e #(parameter int WIDTH = 8, parameter int LANES = 2)
 (input logic [LANES-1:0][WIDTH-1:0] a,
  output logic [LANES-1:0][2*WIDTH-1:0] y);
 generate for (genvar k = 0; k < LANES; k++) begin : lanes
   vector_slice_child_e_lane #(.WIDTH(WIDTH)) u (.a(a[k]), .y(y[k]));
 end endgenerate
endmodule
