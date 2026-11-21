// A source-shaped always_comb self-read. IEEE 1800-2023 §9.2.2.2.1
// excludes y from the implicit sensitivity list because the body writes y.
// Canonical E must retain the previous y[0] for the current activation.
module rbw_selfinc (
  input logic a,
  output logic [1:0] y
);
  always_comb begin
    y = {y[0], a};
  end
endmodule
