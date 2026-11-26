module event_generated_repro(input logic clk, input logic d, output logic q);
  generate
    for (genvar i = 0; i < 1; i++) begin : g
      always @(posedge clk) q <= d;
    end
  endgenerate
endmodule
