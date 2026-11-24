// Noisy-multiplier baseline (feasibility prototype), STRUCTURAL form.
//
// Every logic gate is an instance of a gate module with its own fault input
// `f`, which flips the gate's output (y = gate(inputs) ^ f). Wires, constants
// and port copies are plain continuous assigns and contain no logic.
//
// The fault vector is one packed 2-D input `f[4N-4:0][N-1:0]`, i.e. exactly
// G(N) = (4N - 3) * N bits, one per gate instance, bit (r, j) = flat bit
// r*N + j:
//   row r = i            (0 <= i < N)      : AND gate pp[i][j]
//   row r = N + 3(i-1)   (1 <= i < N)      : xor t[i][j]
//   row r = N + 3(i-1)+1                   : xor s[i][j]
//   row r = N + 3(i-1)+2                   : maj c[i][j+1]
// so G(N) = N^2 AND gates + 3 N (N-1) full-adder gates.
//
// Netlist: the array multiplier of svgolf's mul_n reference (row i adds
// pp[i] to the upper N bits of row i-1), each full adder as two xor2f and
// one maj3f. f = 0 is the fault-free run.

module and2f (input logic a, b, f, output logic y);
  assign y = (a & b) ^ f;
endmodule

module xor2f (input logic a, b, f, output logic y);
  assign y = (a ^ b) ^ f;
endmodule

module maj3f (input logic a, b, c, f, output logic y);
  assign y = ((a & b) | (a & c) | (b & c)) ^ f;
endmodule

module noisy_mul #(parameter int N = 4) (
  input  logic [N-1:0]          a, b,
  input  logic [4*N-4:0][N-1:0] f,
  output logic [2*N-1:0]        p
);
  logic [N-1:0][N-1:0] pp;   // pp[i][j] = a[j] & b[i]
  logic [N-1:0][N:0]   s;    // row sums (N+1 bits)
  logic [N-1:0][N:0]   c;    // ripple carries
  logic [N-1:0][N-1:0] t;    // propagate

  genvar i, j;
  generate
    for (i = 0; i < N; i++) begin : g_pp
      for (j = 0; j < N; j++) begin : g_pp_j
        and2f u_and (.a(a[j]), .b(b[i]), .f(f[i][j]), .y(pp[i][j]));
      end
    end
  endgenerate

  assign s[0] = {1'b0, pp[0]};
  assign c[0] = '0;
  assign t[0] = '0;

  generate
    for (i = 1; i < N; i++) begin : g_row
      assign c[i][0] = 1'b0;
      for (j = 0; j < N; j++) begin : g_bit
        xor2f u_t (.a(s[i-1][j+1]), .b(pp[i][j]), .f(f[N+3*i-3][j]), .y(t[i][j]));
        xor2f u_s (.a(t[i][j]), .b(c[i][j]), .f(f[N+3*i-2][j]), .y(s[i][j]));
        maj3f u_c (.a(s[i-1][j+1]), .b(pp[i][j]), .c(c[i][j]), .f(f[N+3*i-1][j]), .y(c[i][j+1]));
      end
      assign s[i][N] = c[i][N];
    end
  endgenerate

  generate
    for (i = 0; i < N; i++) begin : g_out
      assign p[i] = s[i][0];
    end
  endgenerate
  assign p[2*N-1:N] = s[N-1][N:1];
endmodule
