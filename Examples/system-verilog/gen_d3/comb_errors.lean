import Examples.«system-verilog».gen_d3.gen
import LeanModels.Sv.CombViewTactic

/-!
# Selects of a three-dimensional packed declaration (`Examples/system-verilog/gen_d3/neg`)

`gen_d3_sel`: `y = t[1][0][2]`, a cell of a 3-D declaration: refused until tac8 (a 3-D declaration was read as a whole
signal), read since (`Acc.cell3`, the nested row-major offset `rmN 3 (rmN N 1 0) 2`); its structure is proved here.
`gen_d3_nz`: the same select of a declaration whose plane range is `[2:1]`: the selects of a 3-D declaration are read over
zero-based descending ranges only, so the select is refused, naming the declaration.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_d3.gen

namespace Examples.«system-verilog».gen_d3.comb_errors

/-- The cell select is read (tac8): the structure at every `1 ≤ N < 2^20`. -/
example (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) : CombDesign (gen_d3_sel.sem N) := by
  sv_structure
  all_goals (intros; first | omega | (sv_rowmajor; (try simp only [true_and]); omega))

/--
error: sv_structure: outside the supported fragment — site `plain#1`: `t`: element selects need zero-based descending dimensions `[hi:0][hi:0][hi:0]`
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) : CombDesign (gen_d3_nz.sem N) := by
  sv_structure

end Examples.«system-verilog».gen_d3.comb_errors
