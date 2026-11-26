package pts_base;
  parameter int unsigned SW = 4;
  // A typedef whose width is a parameter of its own package.
  typedef logic [SW-1:0] sel_t;
  parameter int unsigned HW = 3;
  typedef logic [HW-1:0] handle_t;
endpackage
package pts_cfg;
  parameter int unsigned N = 4;
  // A system function of a package parameter in the width.
  typedef logic [$clog2(N)-1:0] pos_t;
  // A typedef of another package's typedef.
  typedef pts_base::sel_t my_sel_t;
  parameter int unsigned LANES = 2;
  // A typedef of a packed array of another package's typedef.
  typedef pts_base::handle_t [LANES-1:0] handles_t;
  // A constant typed by the typedef chain.
  localparam my_sel_t SEL_INIT = 4'd9;
  typedef struct packed { logic [7:0] x; logic [7:0] y; } pair_t;
  // A packed array of packed structs.
  localparam pair_t [1:0] PAIRS = {{8'd1, 8'd2}, {8'd3, 8'd4}};
endpackage
