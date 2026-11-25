// the memory-only quiescence shape inside a child instance
module a4_q_child (input logic seed, output logic q, output logic r);
  logic mem [0:1];
  always_comb mem[1] = mem[0];
  always_comb mem[0] = seed;
  assign q = 1'b0;
  assign r = mem[1];
endmodule
module a4_q_hier_mem (input logic seed, output logic q, output logic r);
  a4_q_child u (.seed(seed), .q(q), .r(r));
endmodule
