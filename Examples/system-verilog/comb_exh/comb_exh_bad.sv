// The table of `comb_exh_table.sv` with one wrong item (11 has three ones, the table says two): `sv_exhaustive`
// must refuse it, naming the input and the first differing output bit (`exh_errors.lean`).
module comb_exh_bad (
    input  logic [3:0] x,
    output logic [2:0] y
);
  always_comb begin
    case (x)
      4'd0: y = 3'd0;
      4'd1: y = 3'd1;
      4'd2: y = 3'd1;
      4'd3: y = 3'd2;
      4'd4: y = 3'd1;
      4'd5: y = 3'd2;
      4'd6: y = 3'd2;
      4'd7: y = 3'd3;
      4'd8: y = 3'd1;
      4'd9: y = 3'd2;
      4'd10: y = 3'd2;
      4'd11: y = 3'd2;
      4'd12: y = 3'd2;
      4'd13: y = 3'd3;
      4'd14: y = 3'd3;
      4'd15: y = 3'd4;
      default: y = 3'd0;
    endcase
  end
endmodule
