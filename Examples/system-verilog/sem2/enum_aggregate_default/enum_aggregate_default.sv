package enum_aggregate_default_pkg;
  typedef enum logic [1:0] {MODE_OFF = 2'b00, MODE_ON = 2'b01} mode_t;
  typedef struct packed { logic lock; mode_t mode; } cfg_t;
  parameter cfg_t CFG [0:1] = '{
    '{lock: 1'b0, mode: MODE_OFF},
    '{lock: 1'b0, mode: MODE_OFF}
  };
endpackage
module enum_aggregate_default(input logic x, output logic y);
  import enum_aggregate_default_pkg::*;
  assign y = x;
endmodule
