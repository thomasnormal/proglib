module vector_multiplier_array_instance_e_lane #(parameter int WIDTH = 8)
  (input logic clk, input logic [WIDTH-1:0] a,
   output logic [2*WIDTH-1:0] y);
  always_ff @(posedge clk) y <= {WIDTH'(0), a};
endmodule

module vector_multiplier_array_instance_e #(parameter int WIDTH = 8, parameter int LANES = 2)
  (input logic clk, input logic [WIDTH-1:0] a [0:LANES-1],
   output logic [2*WIDTH-1:0] y [0:LANES-1]);
  generate for (genvar k = 0; k < LANES; k++) begin : lanes
    vector_multiplier_array_instance_e_lane #(.WIDTH(WIDTH)) u
      (.clk(clk), .a(a[k]), .y(y[k]));
  end endgenerate
endmodule
