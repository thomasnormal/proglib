module nd_rows_swap(input logic clk_a, clk_b, input logic seed, output logic a, b);
  always_ff @(posedge clk_a) if (seed) a <= 1'b0; else a <= b;
  always_ff @(posedge clk_b) if (seed) b <= 1'b1; else b <= a;
endmodule
module nd_rows_caseeq(input logic clk, input logic a, output logic b);
  always_ff @(posedge clk)
    if (a === a) b <= 1'b1; else b <= 1'b0;
endmodule
module nd_rows_unknown_index(input logic clk, input logic idx, output logic [3:0] a);
  always_ff @(posedge clk) a[idx] <= 1'b1;
endmodule
module nd_rows_x_if(input logic clk, input logic a, output logic p, q);
  always_ff @(posedge clk) begin
    if (a) p <= 1'b1; else p <= 1'b0;
    if (a) q <= 1'b1; else q <= 1'b0;
  end
endmodule
module nd_rows_ternary(input logic clk, input logic a, output logic b);
  always_ff @(posedge clk) b <= a ? 1'b1 : 1'b0;
endmodule
module nd_rows_xor(input logic clk, input logic a, output logic b);
  always_ff @(posedge clk) b <= a ^ a;
endmodule
module nd_rows_wake(input logic clk, output logic g, output integer count);
  always @(posedge clk) begin g = 1'b0; g <= 1'b1; end
  always @(posedge g) count <= count + 1;
  initial begin g = 1'b1; count = 1; end
endmodule
