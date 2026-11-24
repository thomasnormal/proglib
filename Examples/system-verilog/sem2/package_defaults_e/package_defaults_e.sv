package package_defaults_e_cfg;
  parameter int unsigned ENTRIES = 4;
  parameter int unsigned LANES = 2;
  parameter int unsigned WIDTH = 8;
  typedef logic [7:0] word_t;
  typedef struct packed { logic [31:0] t_refi; logic [31:0] t_zq; } timing_t;
  parameter timing_t DDR = 64'h0000145005161556;
endpackage

package package_defaults_e_derived;
  parameter int unsigned WORKER_W = $clog2(package_defaults_e_cfg::ENTRIES);
endpackage

module package_defaults_e_default #(parameter int unsigned SLOTS = package_defaults_e_cfg::ENTRIES) (
  input logic [SLOTS-1:0] i, output logic [SLOTS-1:0] o);
  assign o = i;
endmodule

module package_defaults_e_chain #(parameter int unsigned W = package_defaults_e_derived::WORKER_W) (
  input logic [W-1:0] i, output logic [W-1:0] o);
  assign o = i;
endmodule

module package_defaults_e_struct #(parameter int unsigned T_REFI = package_defaults_e_cfg::DDR[63:32]) (
  input logic [T_REFI-1:0] i, output logic [T_REFI-1:0] o);
  assign o = i;
endmodule

module package_defaults_e_typed (
  input package_defaults_e_cfg::word_t i,
  output logic [package_defaults_e_cfg::WIDTH-1:0] o);
  assign o = i;
endmodule

module package_defaults_e_localgen (
  input logic [package_defaults_e_cfg::LANES-1:0] i,
  output logic [package_defaults_e_cfg::LANES-1:0] o);
  localparam int unsigned L = package_defaults_e_cfg::LANES;
  genvar k;
  generate for (k = 0; k < L; k++) begin : g_lane
    assign o[k] = i[k];
  end endgenerate
endmodule

module package_defaults_e (
  input logic [3:0] i_default,
  output logic [3:0] o_default,
  input logic [1:0] i_chain,
  output logic [1:0] o_chain,
  input logic [1:0] i_local,
  output logic [1:0] o_local,
  input package_defaults_e_cfg::word_t i_typed,
  output logic [package_defaults_e_cfg::WIDTH-1:0] o_typed);
  logic [3:0] default_value;
  logic [1:0] chain_value;
  logic [5199:0] struct_value;
  package_defaults_e_default default_instance(.i(i_default), .o(default_value));
  package_defaults_e_chain chain_instance(.i(i_chain), .o(chain_value));
  package_defaults_e_struct struct_instance(.i('0), .o(struct_value));
  package_defaults_e_typed typed_instance(.i(i_typed), .o(o_typed));
  package_defaults_e_localgen local_instance(.i(i_local), .o(o_local));
  assign o_default = default_value;
  assign o_chain = chain_value;
endmodule
