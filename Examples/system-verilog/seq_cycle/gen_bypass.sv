// An optional register stage chosen by a conditional generate construct (IEEE 1800-2017 27.5): with REG > 0 an
// enabled register (declared inside the generate block) drives q, with REG = 0 the data passes through.
module gen_bypass #(parameter int W = 4, parameter int REG = 1)
  (input logic clk, en, input logic [W-1:0] d, output logic [W-1:0] q);
  generate if (REG > 0) begin : g_reg
    logic [W-1:0] r;
    always_ff @(posedge clk) if (en) r <= d;
    assign q = r;
  end else begin : g_wire
    assign q = d;
  end endgenerate
endmodule
