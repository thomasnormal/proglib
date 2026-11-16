module event_always_repro(input logic clk, input logic d, output logic q);
  always @(posedge clk) begin
    #1 q <= d;
  end
endmodule
