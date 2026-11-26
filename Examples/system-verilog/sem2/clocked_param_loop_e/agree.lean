import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
import LeanModels.Sv.SeqCycleStages
namespace Examples.«system-verilog».sem2.clocked_param_loop_e.agree
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 loop from "Examples/system-verilog/sem2/clocked_param_loop_e/clocked_param_loop_e.sv.json"
#guard match loop.sem 4 3 with | .ok _ => true | _ => false
#guard match loop.e 4 3 with | .ok d => d.processes.size == 2 | _ => false
#guard match PDesign.instantiateE2 loop.pdesign [4, 3] with | .ok d => d.memories.size == 1 | _ => false

/-!
The ordinary E route admits the source-shaped memory loop.  The clocked
cycle model has a narrower header language and refuses the descending
`DEPTH - 1` / `i > 0` form by name instead of silently replacing it with an
ascending model.
-/

/--
error: sv_structure: process 0 (an edge process) has a procedural `for` loop whose header the clocked stages do not evaluate: they read `for (i = a; i < P; i++)` and `i <= P` (a literal start `a`, a parameter bound `P`, a unit step `i++` or `i = i + 1`) as the route's value list in closed form; any other header (another step, a bound that is not a parameter, a descending loop) is refused
-/
#guard_msgs (whitespace := lax) in
set_option maxHeartbeats 1000000 in
example (W N : Nat) (hW1 : 1 ≤ W) (hW2 : W < 2 ^ 30) (h1 : 1 ≤ N) (h2 : N ≤ 4000) :
    SeqDesign (loop.e W N) "clk" := by
  sv_structure
end Examples.«system-verilog».sem2.clocked_param_loop_e.agree
