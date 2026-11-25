// an always_comb that only reads a memory an edge process writes (now refused by 921d48adf?)
module a4_q_comb_mem_read (input logic clk, input logic [7:0] d, output logic [7:0] r);
  logic [7:0] m [0:1];
  always_ff @(posedge clk) m[0] <= d;
  always_comb r = m[0];
endmodule
