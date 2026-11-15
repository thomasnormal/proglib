module constant_function_module_e #(parameter integer N = 8) (
    output logic [7:0] y);
  function automatic integer DepthW(input integer depth);
    return (depth > 1) ? $clog2(depth) : 1;
  endfunction
  localparam integer W = DepthW(N);
  logic [W-1:0] z;
  assign y = W;
  assign z = W;
endmodule
