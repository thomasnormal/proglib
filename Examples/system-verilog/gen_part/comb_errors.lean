import Examples.«system-verilog».gen_part.gen
import LeanModels.Sv.CombViewTactic

/-!
# An indexed part select outside the affine reading (`Examples/system-verilog/gen_part/neg`)

* `gen_part_sq`: `a[i*i +: 2]`: the base is a product of two genvars, not affine; the select is refused, naming it.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_part.gen

namespace Examples.«system-verilog».gen_part.comb_errors

/--
error: sv_structure: outside the supported fragment — site `g_out#0`: a bound of `a[…+:…]` is not affine (dynamic or nonlinear)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 15) : CombDesign (gen_part_sq.sem N) := by
  sv_structure

end Examples.«system-verilog».gen_part.comb_errors
