module invalid_chain2_wall(input logic [3:0] terms [0:3], output logic [3:0] result);
  generate
    for (genvar row = 0; row < 4; row = row + 1) begin : chain
      wire [3:0] running_sum;
      if (row == 0) begin : first
        assign running_sum = terms[row];
      end else begin : later
        assign running_sum = terms[row] | chain[row - 1].running_sum;
      end
    end
  endgenerate
  assign result = chain[3].running_sum;
endmodule
