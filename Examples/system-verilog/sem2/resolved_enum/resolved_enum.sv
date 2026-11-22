// IEEE 1800-2023 §§6.3.1, 6.19. A four-state enum retains each member's bits.
package states;
  typedef enum logic [3:0] { X_VALUE = 4'bx010, Z_VALUE = 4'bz101,
                             MIXED = 4'bxz01, KNOWN = 4'b0011 } state_t;
endpackage

module resolved_enum(output wire [3:0] x, z, mixed, known);
  assign x = states::X_VALUE;
  assign z = states::Z_VALUE;
  assign mixed = states::MIXED;
  assign known = states::KNOWN;
endmodule
