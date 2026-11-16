// IEEE 1800-2023 §9.6: one time-zero procedural initialization.
module initial_storage_e(output logic q);
  initial begin
    q = 1'b0;
  end
endmodule
