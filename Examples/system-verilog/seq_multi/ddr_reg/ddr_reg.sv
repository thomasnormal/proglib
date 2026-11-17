// A register on each edge of one clock (a double-data-rate capture): the design's events are posedge clk and
// negedge clk (IEEE 1800-2023 §9.4.2).
module ddr_reg #(parameter int W = 4) (
  input  logic clk,
  input  logic [W-1:0] d,
  output logic [W-1:0] qp, qn
);
  always_ff @(posedge clk) qp <= d;
  always_ff @(negedge clk) qn <= d;
endmodule
