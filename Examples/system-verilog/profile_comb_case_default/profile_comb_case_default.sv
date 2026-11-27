module profile_comb_case_default(input logic clk, input logic [1:0] sel, input logic [3:0] a, input logic [3:0] b,
           output logic [3:0] comb, output logic [3:0] q);
  always_comb begin
    case (sel)
      2'b00: comb = a;
      2'b01: comb = b;
      default: comb = 4'bxxxx;
    endcase
  end
  always_ff @(posedge clk) q <= a;
endmodule
