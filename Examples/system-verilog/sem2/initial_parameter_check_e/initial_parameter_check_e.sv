module initial_parameter_check #(
  parameter int N = 1
) (
  output logic y
);
  initial begin
    assert (N > 0) else $error("N must be positive");
  end
  assign y = (N > 0);
endmodule
