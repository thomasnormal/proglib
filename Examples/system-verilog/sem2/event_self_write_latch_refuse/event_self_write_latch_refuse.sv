// IEEE 1800-2023 §9.4.2: a blocking self-write is not sensitive while active,
// but re-arms the explicit event control when the process returns.
module event_self_write_list(input logic a, output logic t, output logic y);
  always @(a or t) begin
    y = t;
    t = a;
  end
endmodule
module event_self_write_latch(input logic en, input logic a, output logic t, output logic y);
  always @(en or a or t) begin
    if (en) begin
      y = t;
      t = a;
    end
  end
endmodule
