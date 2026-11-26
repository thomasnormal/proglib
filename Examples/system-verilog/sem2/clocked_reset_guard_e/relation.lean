import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.NdSound

/-!
# An async-reset flop is in the fragment of the executor soundness theorem

```systemverilog
module clocked_reset_guard_e(input logic clk, input logic rst_n, input logic d, output logic q);
always_ff @(posedge clk or negedge rst_n) begin
  if (!rst_n) q <= 1'b0;
  else q <= d;
end
endmodule
```

A second instance of `CoreMemDesign.step_sound`, on a body with an `if` and
an asynchronous reset.  `E_nbaClocked` is decided by the kernel on the loaded
design, so the fragment `CoreMemDesign.NbaClocked` is not only the swap.

What is and is not shown here: the design is in the fragment, and the two
soundness theorems are instantiated on it with their start hypotheses left
visible (a typed store; clock and reset known before the row and in the
executor's result).  That the executor returns on some row of this design is
NOT proved in this file; `agree.lean` in this directory evaluates such rows
with `#guard`.  No simulator was run for this file.
-/

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».sem2.clocked_reset_guard_e.relation

load_design_sv2 guard from "Examples/system-verilog/sem2/clocked_reset_guard_e/clocked_reset_guard_e.sv.json"

def E : CoreMemDesign := match guard.e with | .ok d => d | _ => default

set_option maxRecDepth 100000

theorem E_ok : guard.e = .ok E := by rfl

/-- The clock and the asynchronous reset are the control signals. -/
theorem E_sources : E.ndEventSources = ["clk", "rst_n"] := by decide

/-- The design is in the fragment: each field is decided by the kernel. -/
theorem E_nbaClocked : E.NbaClocked :=
  { admitted := by decide
    bodies := by decide
    fourState := by decide
    edgeBase := by rfl }

/-- `step_sound` on this design: from a typed store with `clk` and `rst_n`
known, an executor result with `clk` and `rst_n` known is the end of a settled
run of the relation under the executor's choices. -/
theorem flop_step_sound (st next : CoreMemState) (entry : SvState)
    (hT : E.scalar.Typed st.scalar) (hk : E.ControlsKnown st)
    (h : E.step st entry = .ok next) (hk' : E.ControlsKnown next) :
    ∃ t, Nd.EventSettles E st entry Oracle.zero t ∧ t.store = next ∧ t.oracle = Oracle.zero :=
  CoreMemDesign.step_sound E_nbaClocked hT hk h hk'

/-- The row-list form on this design. -/
theorem flop_rows_sound (rows : List SvState) (st : CoreMemState) (out : List CoreMemState)
    (hT : E.scalar.Typed st.scalar) (hk : E.ControlsKnown st)
    (hrows : ∀ row ∈ rows, (row.isEmpty && E.scalarAssignInputsOnly) = false)
    (h : runCoreMemRows E st rows = .ok out) (hout : ∀ st' ∈ out, E.ControlsKnown st') :
    Nd.Trace E st Oracle.zero rows out Oracle.zero :=
  runCoreMemRows_sound E_nbaClocked rows st out hT hk hrows h hout

#print axioms E_nbaClocked
#print axioms flop_step_sound
#print axioms flop_rows_sound

end Examples.«system-verilog».sem2.clocked_reset_guard_e.relation
