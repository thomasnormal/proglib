module wake_base_wrong_answer_e(
    input logic init,
    input logic clk,
    output logic g,
    output integer count
);
  always @(posedge init) begin
    g <= 1'b1;
    count <= 0;
  end
  always @(posedge clk) begin
    g = 1'b0;
    g <= 1'b1;
  end
  always @(posedge g) begin
    count = count + 1;
  end
endmodule
