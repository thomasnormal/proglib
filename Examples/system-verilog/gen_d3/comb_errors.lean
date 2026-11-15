import Examples.«system-verilog».gen_d3.gen
import LeanModels.Sv.CombViewTactic

/-!
# A select of a three-dimensional packed declaration (`Examples/system-verilog/gen_d3/neg`)

`gen_d3_sel`: `y = t[1][0][2]`: a 3-D declaration is read as a whole signal; the access forms of a select of one (a
bit, a row of a plane, a plane) are not built, so the select is refused, naming it.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_d3.gen

namespace Examples.«system-verilog».gen_d3.comb_errors

/--
error: sv_structure: outside the supported fragment — site `plain#1`: a select of the three-dimensional declaration `t` (outside the fragment: a 3-D declaration is read as a whole signal; selects are read of 1-D and 2-D declarations)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) : CombDesign (gen_d3_sel.sem N) := by
  sv_structure

end Examples.«system-verilog».gen_d3.comb_errors
