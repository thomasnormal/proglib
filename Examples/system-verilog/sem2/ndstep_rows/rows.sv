module nd_rows_swap(input logic clk_a, clk_b, input logic seed, output logic a, b);
  always_ff @(posedge clk_a) if (seed) a <= 1'b0; else a <= b;
  always_ff @(posedge clk_b) if (seed) b <= 1'b1; else b <= a;
endmodule
module nd_rows_xclock(input logic clk_a, clk_b, output logic a, b);
  always_ff @(posedge clk_a) a <= b;
  always_ff @(posedge clk_b) b <= a;
endmodule
module nd_rows_race01(input logic clk, output logic a);
  initial a = 1'bx;
  always @(posedge clk) a = 1'b0;
  always @(posedge clk) a = 1'b1;
endmodule
module nd_rows_race10(input logic clk, output logic a);
  initial a = 1'bx;
  always @(posedge clk) a = 1'b1;
  always @(posedge clk) a = 1'b0;
endmodule
module nd_rows_caseeq(input logic clk, input logic a, output logic b);
  always_ff @(posedge clk)
    if (a === a) b <= 1'b1; else b <= 1'b0;
endmodule
module nd_rows_casez(input logic clk, input logic a, output logic b);
  always_ff @(posedge clk)
    casez (a) 1'bx: b <= 1'b1; default: b <= 1'b0; endcase
endmodule
module nd_rows_casex(input logic clk, input logic a, output logic b);
  always_ff @(posedge clk)
    casex (a) 1'bx: b <= 1'b1; default: b <= 1'b0; endcase
endmodule
module nd_rows_caseeq_index(input logic clk, output logic [3:0] a);
  logic b;
  initial begin a = 4'b0; b = 1'bx; end
  always @(posedge clk) a[b === b] <= 1'b1;
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
module nd_rows_nba_xclock(input logic clk, output logic g);
  logic a;
  initial a = 1'bx;
  always_ff @(posedge clk) g <= a;
endmodule
module nd_rows_wake(input logic clk, output logic g, output integer count);
  always @(posedge clk) begin g = 1'b0; g <= 1'b1; end
  always @(posedge g) count <= count + 1;
  initial begin g = 1'b1; count = 1; end
endmodule
