module pts_leaf #(parameter int unsigned P = 2) (
  input  pts_base::sel_t a,
  input  pts_cfg::pos_t [P-1:0] b,
  input  pts_cfg::my_sel_t c,
  input  pts_cfg::handles_t d,
  input  logic [pts_base::SW-1:0] e,
  output pts_base::sel_t oa,
  output pts_cfg::pos_t [P-1:0] ob,
  output pts_cfg::my_sel_t oc,
  output pts_cfg::handles_t od,
  output logic [pts_base::SW-1:0] oe,
  output logic [7:0] op,
  output pts_base::handle_t om);
  localparam pts_base::sel_t K = pts_base::sel_t'(5);
  localparam pts_cfg::my_sel_t K2 = pts_cfg::SEL_INIT;
  pts_base::sel_t v;
  pts_base::handle_t [P-1:0] w;
  // An unpacked array whose element is a package typedef.
  pts_base::handle_t mem [P];
  assign v = a ^ K;
  assign oa = v;
  assign ob = b;
  assign oc = c ^ K2;
  assign w = d;
  assign od = w;
  assign oe = e;
  assign op = {4'd0, pts_cfg::SEL_INIT};
  assign mem[0] = d[0];
  assign om = mem[0];
endmodule
