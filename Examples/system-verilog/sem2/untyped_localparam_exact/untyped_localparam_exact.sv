// IEEE 1800-2023 §§6.20.2, 11.6.1: untyped constants take the initializer type.
// Xcelium follows the final-value width required by the standard.  Icarus 13.0
// retains lossless intermediate width for WIDE, which is recorded as an oracle
// deviation in harness/sv/cases2.json.
module untyped_localparam_exact #(parameter int N = 10000)
  (output logic [31:0] k, output logic [31:0] a,
   output logic [31:0] u, output logic [31:0] p,
   output logic [31:0] ls, output logic [31:0] rs,
   output logic [31:0] neg, output logic [31:0] cat,
   output logic [31:0] signed_kw, output logic [31:0] range_only,
   output logic [31:0] observed, output logic [31:0] observed_w);
  localparam K = (N * 1000000) / 1000000;
  localparam A = (N + 32'sd2147483647) % 1000;
  localparam U = 8'd5 + 8'd1;
  localparam P = 2 ** 8;
  localparam LS = 8'd1 << 2;
  localparam RS = 8'd128 >> 1;
  localparam NEG = -8'd5;
  localparam CAT = {4'hA, 4'h5};
  localparam signed SK = 4'b1000;
  localparam [3:0] RO = 4'b1111;
  localparam OBS = N + 1;
  localparam WIDE = 8'd5 + 1'b1;
  localparam OBSW = {4'hF, WIDE};
  assign k = K;
  assign a = A;
  assign u = U;
  assign p = P;
  assign ls = LS;
  assign rs = RS;
  assign neg = NEG;
  assign cat = CAT;
  assign signed_kw = SK;
  assign range_only = RO;
  assign observed = OBS;
  assign observed_w = OBSW;
endmodule
