// Clean-room package-constant wall for IEEE 1800-2023 §5.7.1 and §10.8.
module package_fill_concat_e #(parameter integer W = 4) (
    output logic [W:0] k0,
    output logic [W:0] k1,
    output logic [1:0] u0,
    output logic [1:0] u1
);
  localparam logic [W:0] K0 = {'0, 1'b1};
  localparam logic [W:0] K1 = {1'b1, '0};
  localparam U0 = {'0, 1'b1};
  localparam U1 = {1'b1, '1};
  assign k0 = K0;
  assign k1 = K1;
  assign u0 = U0;
  assign u1 = U1;
endmodule
