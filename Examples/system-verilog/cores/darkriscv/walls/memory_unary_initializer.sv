// Clean-room canonical-memory row for an INT-class scalar initializer.
// IEEE 1800-2023 §§6.8 and 11.8 size the constant at the declaration width.
`timescale 1ns/1ns
module memory_unary_initializer #(parameter int DEPTH = 1) (output logic [1:0] q);
  logic [1:0] value = -1;
  logic [1:0] mem [0:DEPTH-1];

  initial begin
    mem[0] = value;
  end

  assign q = mem[0];
endmodule
