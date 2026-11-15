// Generic parameter-sized storage witness for the canonical equation-gate boundary.
// The direct structure gate admits the declaration; the conservative equation gate rejects the procedural comb update.
module parameterized_storage_structure #(parameter int N = 2)(
  input logic [7:0] x,
  output logic [7:0] y
);
  logic [7:0] stage [0:N-1];
  always_comb begin
    stage[0] = x;
    y = stage[0];
  end
endmodule
