import Examples.«system-verilog».gen_deep.gen
import LeanModels.Sv.CombViewTactic

/-!
# Two blocks with one label at one depth (`Examples/system-verilog/gen_deep/neg`)

`gen_deep_dup`: the blocks `g_x[0].g_b` and `g_y[0].g_b` are distinct scopes (IEEE 1800-2023 §27.6). The summary names a
site by its innermost block, its position there and its depth (`LSite.key`); where a label labels more than one loop of
the design the block is named by its label path (`qualifyFams`), so the two families are `g_x.g_b` and `g_y.g_b`
and the design is accepted. (Before, the structural check refused it: "two sites share the identity (`g_b#0[i, j]` and
`g_b#0[i, j]`)"; the file keeps its name.)
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_deep.gen

namespace Examples.«system-verilog».gen_deep.comb_errors

-- the two families' block names: the label paths
#guard (gen_deep_dup.pdesign.summary.toOption.map fun s => s.lsites.map (·.blk)) == some ["g_x.g_b", "g_y.g_b"]

/-- The structure of `gen_deep_dup`, at every `1 ≤ N < 2^30`. -/
theorem gen_deep_dup_comb (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 30) : CombDesign (gen_deep_dup.sem N) := by
  sv_structure
  all_goals (intros; first | omega | (sv_rowmajor; (try simp only [true_and]); omega))

end Examples.«system-verilog».gen_deep.comb_errors
