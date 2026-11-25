// an initial process that fills a memory (now refused by 921d48adf?)
module a4_q_init_mem (input logic [1:0] a, output logic [7:0] r);
  logic [7:0] m [0:3];
  initial begin m[0] = 8'd1; m[1] = 8'd2; m[2] = 8'd3; m[3] = 8'd4; end
  assign r = m[a];
endmodule
