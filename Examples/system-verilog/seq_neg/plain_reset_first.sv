// Refused by an obligation, not by the profile: a plain `always` whose event list names the reset first. The first
// edge of the list is read as the clock, so the body reads its "clock" (`rst_n`) as data.
module plain_reset_first #(parameter int N = 4) (input logic clk, rst_n, input logic [N-1:0] d,
    output logic [N-1:0] q);
  always @(negedge rst_n or posedge clk)
    if (!rst_n) q <= '0;
    else q <= d;
endmodule
