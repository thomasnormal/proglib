// Clean-room census witness: three independent source-shaped admission walls.
// IEEE 1800-2023 §6.19/§11.5.1 leaves the parameter-dependent aggregate
// layout and query-label selects outside this ordinary slice.
module refusal_census_three_walls #(parameter int N = 3) (
  input logic [N-1:0] a,
  input logic [31:0] v,
  input logic [1:0] b,
  output logic [1:0] o1,
  output logic [1:0] o2,
  output logic [31:0] y
);
  typedef struct packed { logic [N-1:0] x; logic [1:0] y; } st_t;
  typedef union packed { logic [N-1:0] x; logic [N-1:0] y; } u_t;
  st_t s;
  u_t uv;
  assign s = {a, b};
  assign uv = a;
  assign o1 = v[$clog2($bits(s)) +: 2];
  assign o2 = v[$bits(uv) +: 2];
  always_comb begin
    y = '0;
    y[$bits(s) - 1 -: 2] = b;
  end
endmodule
