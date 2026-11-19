// IEEE 1800-2023 §§4.5 and 10.3: source order need not be topological.
module time_zero_quiesce_nontopo(output logic a, output logic b);
  assign a = b;
  assign b = 1'b1;
endmodule
