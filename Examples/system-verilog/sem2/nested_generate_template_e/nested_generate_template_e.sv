module nested_generate_template_e #(parameter int N = 2)(output wire [N-1:0] y);
  genvar i;
  for (i = 0; i < N; i++) begin : g
    for (genvar j = 0; j < i; j++) begin : h
      assign y[i] = 1'b1;
    end
  end
endmodule
