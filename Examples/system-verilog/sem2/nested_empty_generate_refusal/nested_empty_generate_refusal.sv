module nested_empty_generate_refusal #(parameter int J = 2)(output wire [J-1:0] y);
  genvar j;
  generate
    for (j = 0; j < J; j++) begin : outer
      genvar k;
      for (k = 0; k < j; k++) begin : inner
        assign y[j] = 1'b1;
      end
    end
  endgenerate
endmodule
