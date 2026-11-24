// Fixed-depth FIFO used by the column-A engine increments.
// A push or pop is accepted only when the corresponding pre-state is
// non-full or non-empty.  Simultaneous accepted push and pop preserve both
// operations and leave the level unchanged.
module parameterized_fifo_canonical_e #(
  parameter int DATA_W = 32,
  parameter int DEPTH = 16
) (
  input  logic             clk,
  input  logic             rst_n,
  input  logic             push,
  input  logic             pop,
  input  logic [DATA_W-1:0] push_data,
  output logic [DATA_W-1:0] head,
  output logic             empty,
  output logic             full,
  output logic [$clog2(DEPTH+1)-1:0] level,
  output logic             push_accepted,
  output logic             pop_accepted
);
  localparam int PTR_W = $clog2(DEPTH);
  logic [DATA_W-1:0] storage [0:DEPTH-1];
  logic [PTR_W-1:0] read_ptr;
  logic [PTR_W-1:0] write_ptr;

  assign empty = (level == 0);
  // The parameter is intentionally compared in its natural integer form.
  // The width diagnostic is local to this parameterized comparison.
  /* verilator lint_off WIDTHEXPAND */
  assign full = (level == DEPTH);
  /* verilator lint_on WIDTHEXPAND */
  assign head = storage[read_ptr];
  assign push_accepted = push && !full;
  assign pop_accepted = pop && !empty;

  always_ff @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
      read_ptr <= '0;
      write_ptr <= '0;
      level <= '0;
    end else begin
      if (push_accepted) begin
        storage[write_ptr] <= push_data;
        write_ptr <= write_ptr + 1'b1;
      end
      if (pop_accepted)
        read_ptr <= read_ptr + 1'b1;
      case ({push_accepted, pop_accepted})
        2'b10: level <= level + 1'b1;
        2'b01: level <= level - 1'b1;
        default: level <= level;
      endcase
    end
  end
endmodule
