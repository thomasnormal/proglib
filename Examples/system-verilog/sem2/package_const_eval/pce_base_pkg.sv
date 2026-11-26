package pce_base;
  parameter int unsigned UNITS = 4;
  parameter int NEG = -3;
  localparam logic B1 = 1'b1;
  localparam logic [31:0] W32 = 32'hDEAD_BEEF;
  localparam logic signed [31:0] S32 = -32'sd2;
  localparam logic [32:0] W33 = {1'b1, 32'h0000_0001};
  localparam logic [63:0] W64 = (64'd7 << 32) | 64'd9;
  localparam logic [64:0] W65 = 65'h1_0000_0000_0000_0003;
  localparam logic signed [64:0] S65 = -65'sd5;
  localparam logic [7:0] XZ8 = 8'b1x0z_01zx;
  typedef struct packed { logic [31:0] hi; logic [31:0] lo; } pair_t;
  localparam pair_t PAIR = '{hi: 32'd7, lo: 32'd9};
  typedef struct packed { logic [1023:0] pad; logic [31:0] fa; logic [31:0] fb; } wide_t;
  localparam wide_t WIDE = '{pad: '0, fa: 32'd10, fb: 32'd12};
  localparam logic [1087:0] WX = {8'b1x0z_01zx, 1080'd5};
endpackage
