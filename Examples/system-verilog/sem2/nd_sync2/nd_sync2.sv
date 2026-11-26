// A two-flop synchroniser: d is asynchronous to clk (relational-semantics example).
module nd_sync2 (
    input  logic clk,
    input  logic d,
    output logic s1,
    output logic s2
);
  always_ff @(posedge clk) s1 <= d;
  always_ff @(posedge clk) s2 <= s1;
endmodule
