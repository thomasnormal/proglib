// Clean-room generated-unpacked-array wall: the smallest propagate-array shape.
module prefix_adder_unpacked_array #(parameter int WIDTH = 4) (
    input logic [WIDTH-1:0] a,
    output logic [WIDTH-1:0] y);
  logic [WIDTH-1:0] mem [0:1];
  genvar i;
  generate for (i = 0; i < WIDTH; i++) begin : g
    assign mem[0][i] = a[i];
  end endgenerate
  assign y = mem[0];
endmodule
