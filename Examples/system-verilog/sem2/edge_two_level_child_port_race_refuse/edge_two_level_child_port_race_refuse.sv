// IEEE 1800-2023 §§4.7 and 10.4.1: a parent blocking write races with a grandchild edge reader.
module edge_two_level_child_port_race_leaf(input logic clk, input logic a, output logic q);
  always_ff @(posedge clk) q <= a;
endmodule
module edge_two_level_child_port_race_mid(input logic clk, input logic a, output logic q);
  edge_two_level_child_port_race_leaf l(.clk(clk), .a(a), .q(q));
endmodule
module edge_two_level_child_port_race(input logic clk, input logic d, output logic q);
  logic a;
  always_ff @(posedge clk) a = d;
  edge_two_level_child_port_race_mid m(.clk(clk), .a(a), .q(q));
endmodule
