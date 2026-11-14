import Examples.«system-verilog».gen_shk.gen
import LeanModels.Sv.CombViewTactic

/-!
# A shift by a literal amount of 32 or more (`Examples/system-verilog/gen_shk/neg`)

`a[i >> 40]`: IEEE 1800-2023 §11.4.10 shifts every bit out (the value is `0`), but `>>` by a literal is an atom only for an
amount in `[0, 32)` (`litAmt?`), so the index is not affine: refused, naming the site.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_shk.gen

namespace Examples.«system-verilog».gen_shk.comb_errors

/--
error: sv_structure: outside the supported fragment — site `g_bit#0`: non-affine genvar-index obligation: read `a[…]` has a dynamic or nonlinear index, so the driven window cannot be determined
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 30) : CombDesign (gen_shk_wide.sem N) := by
  sv_structure

end Examples.«system-verilog».gen_shk.comb_errors
