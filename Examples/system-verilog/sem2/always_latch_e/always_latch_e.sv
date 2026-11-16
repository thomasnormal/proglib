// IEEE 1800-2023 §§9.2.2.3 and 9.4.2: a level-sensitive latch.
module always_latch_e(input logic en, input logic d, output logic q);
  always_latch if (en) q = d;
endmodule
