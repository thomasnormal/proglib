// Outside the clocked profile: a plain `always` on three edges (a clock, a reset and a set). The clocked views read an
// event list of one clock edge with at most one further edge (the asynchronous reset) as an edge process.
module plain_three_events (input logic clk, rst_n, set, input logic d, output logic q);
  always @(posedge clk or negedge rst_n or posedge set)
    if (!rst_n) q <= 1'b0;
    else if (set) q <= 1'b1;
    else q <= d;
endmodule
