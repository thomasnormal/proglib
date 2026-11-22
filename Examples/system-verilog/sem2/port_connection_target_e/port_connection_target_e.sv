// Parser-native aggregate output port target receipt for IEEE 1800-2023 §23.2.2.
typedef struct { logic [3:0] value; } field_t;
typedef struct { field_t fields [0:1]; } register_block_t;
module register_leaf(input logic d, output register_block_t out_state);
  always_comb begin
    out_state.fields[0].value = {4{d}};
  end
endmodule
module register_parent(input logic d, output logic [3:0] y);
  register_block_t state;
  register_leaf u_leaf(.d(d), .out_state(state));
  assign y = state.fields[0].value;
endmodule
