module duplicate_generate_group_e #(parameter int N = 2) (
  input logic [N-1:0] i, output logic [N-1:0] o);
  for (genvar k = 0; k < N; k++) begin : g
    logic t;
    assign t = i[k];
    assign o[k] = t;
  end
  for (genvar j = 0; j < N; j++) begin : g
    logic u;
    assign u = i[j];
  end
endmodule
