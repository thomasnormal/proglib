// Two registers on two independent input clocks and no read between them: the instant view's product case
// (IEEE 1800-2023 §9.4.2: each process wakes on its own clock's rising edge).
module two_reg #(parameter int W = 4) (
  input  logic clka, clkb,
  input  logic [W-1:0] da, db,
  output logic [W-1:0] qa, qb
);
  always_ff @(posedge clka) qa <= da;
  always_ff @(posedge clkb) qb <= db;
endmodule
