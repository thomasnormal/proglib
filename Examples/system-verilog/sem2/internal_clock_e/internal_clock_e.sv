// An edge process driven by a signal generated inside the module.
module internal_clock_repro(input logic enable, input logic data, output logic result);
  logic generated_clock;
  always_comb begin
    generated_clock = enable;
  end
  always_ff @(posedge generated_clock) begin
    result <= data;
  end
endmodule
