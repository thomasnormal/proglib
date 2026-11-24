module generate_scope_unpacked_e #(parameter int N=1) (input logic clk, input logic d, output logic q);
  generate if (N > 0) begin : storage
    logic value [0:1];
    always_ff @(posedge clk) value[0] <= d;
    assign q = value[0];
  end endgenerate
endmodule
