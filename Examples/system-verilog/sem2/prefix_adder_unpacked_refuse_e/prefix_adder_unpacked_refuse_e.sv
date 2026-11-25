module prefix_adder_unpacked_refuse_e #(parameter int WIDTH = 4) (
  input logic [WIDTH-1:0] a, output logic [WIDTH-1:0] y);
  logic [WIDTH-1:0] mem [0:1];
  genvar i;
  generate for (i = 0; i < WIDTH; i++) begin : g
    assign mem[0][i] = a[i];
  end endgenerate
  assign y = mem[0];
endmodule
