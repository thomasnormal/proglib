// IEEE 1800-2023 §6.20.2: an untyped parameter takes its final value type.
module untyped_width_repair #(parameter P = 8'h01) (output logic [7:0] y);
  localparam L = P | 0;
  if (L < 0) begin : g_neg
    assign y = 8'h01;
  end else begin : g_pos
    assign y = 8'h02;
  end
endmodule
