module function_call_expression_repro(input logic in, output logic y);
  always_comb begin
    y = $test$plusargs("flag") ? in : 1'b0;
  end
endmodule
