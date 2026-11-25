// Source-shaped aggregate field continuous assignments from an Ibex-style delay structure.
typedef struct packed {
  logic [3:0] instr;
  logic valid;
  logic [1:0] tag;
} delayed_inputs_t;
module struct_port_assign_e (
  input logic [3:0] instr_i,
  input logic valid_i,
  input logic [1:0] tag_i,
  output logic [6:0] y
);
  delayed_inputs_t shadow_inputs_in;
  assign shadow_inputs_in.instr = instr_i;
  assign shadow_inputs_in.valid = valid_i;
  assign shadow_inputs_in.tag = tag_i;
  assign y = shadow_inputs_in;
endmodule
