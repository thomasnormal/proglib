import Examples.«system-verilog».gen_mulx.gen
import LeanModels.Sv.CombViewTactic

/-!
# Products and shift amounts outside the affine reading (`Examples/system-verilog/gen_mulx/neg`)

* `gen_mulx_quot`: `y[t*(P / 2) +: (P / 2)]`: a genvar times a QUOTIENT atom. The product reading (`affMulLX`) takes a
  form of names times a form of shift and power atoms; a quotient is neither, so the bound is not affine: refused, naming
  the site and the product.
* `gen_mulx_amt`: `a[P >> (l + t)]`: an affine shift amount is ONE name plus or minus a literal (`affAmt?`); the sum of two
  genvars is not one, so the index is not affine: refused, naming the site.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_mulx.gen

namespace Examples.«system-verilog».gen_mulx.comb_errors

/--
error: sv_structure: outside the supported fragment — site `g_t#0`: a bound of `y[…+:…]` is not affine (dynamic or nonlinear) — it holds a product the affine forms do not read: a product is read where one factor is a constant, or where one factor has only names and a constant (genvars, parameters, localparams) and the other only shifts and powers of named constants and a constant (`(3*t)*(P >> (l+1))`)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 30) : CombDesign (gen_mulx_quot.sem N) := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `g_t#0`: non-affine genvar-index obligation: read `a[…]` has a dynamic or nonlinear index, so the driven window cannot be determined
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 30) : CombDesign (gen_mulx_amt.sem N) := by
  sv_structure

end Examples.«system-verilog».gen_mulx.comb_errors
