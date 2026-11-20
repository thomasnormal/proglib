// IEEE 1800-2023 §10.9: fixed unpacked package parameter of packed structs.
package package_aggregate_param_pkg;
  typedef struct packed {
    logic lock;
    logic [1:0] mode;
    logic exec;
    logic write;
    logic read;
  } cfg_t;
  parameter cfg_t P[4] = '{
    '{lock: 1'b0, mode: 2'b00, exec: 1'b0, write: 1'b0, read: 1'b0},
    '{lock: 1'b1, mode: 2'b01, exec: 1'b0, write: 1'b1, read: 1'b0},
    '{lock: 1'b0, mode: 2'b10, exec: 1'b1, write: 1'b0, read: 1'b1},
    '{lock: 1'b1, mode: 2'b11, exec: 1'b1, write: 1'b1, read: 1'b1}
  };
endpackage
module package_aggregate_param_e
  (input logic [1:0] i, output logic [5:0] y);
  assign y = package_aggregate_param_pkg::P[i];
endmodule
