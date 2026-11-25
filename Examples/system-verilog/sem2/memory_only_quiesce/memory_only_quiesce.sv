// IEEE 1800-2023 §§4.5 and 9.2.2.2: only memory changes across active passes.
module memory_only_quiesce(input logic seed, output logic q);
  logic mem [0:1];
  always_comb mem[1] = mem[0];
  always_comb mem[0] = seed;
  assign q = 1'b0;
endmodule
