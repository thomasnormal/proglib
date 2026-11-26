module pcr_gen (output logic [7:0] o);
  assign o[7:3] = 5'b0;
  if (1) begin : w
    // The genvar starts at a negative package constant.
    for (genvar g = pcr::M; g < 0; g++) begin : gl
      assign o[g + 3] = 1'b1;
    end
  end
endmodule
