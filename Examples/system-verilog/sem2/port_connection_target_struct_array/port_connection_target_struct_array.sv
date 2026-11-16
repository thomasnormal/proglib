// Generic generated-register style output connection (IEEE 1800-2023 §23.2.2).
typedef struct { logic [3:0] value; } field_t;
typedef struct { field_t fields [0:1]; } register_block_t;
module register_leaf(input logic d, output register_block_t hwif_out);
  always_comb begin
    hwif_out.fields[0].value = {4{d}};
    hwif_out.fields[1].value = 4'b0;
  end
endmodule
module register_parent(input logic d, output logic [3:0] y);
  register_block_t state;
  register_leaf u_leaf(.d(d), .hwif_out(state));
  assign y = state.fields[0].value;
endmodule
