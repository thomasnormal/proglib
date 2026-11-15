import Examples.«system-verilog».gen_bit.gen
import LeanModels.Sv.CombViewTactic

/-!
# Bit tests and shifts outside the atoms (`Examples/system-verilog/gen_bit/neg`)

* `gen_bit_two`: `((i >> l) & 2) == 2` tests bit `l + 1`; only `(m >> n) & 1` is the bit atom (`xatOf?`), so the
  condition is refused, naming the guard fragment.
* `gen_bit_sum`: `a[(i + 1) >> 1]`: only a name is shifted, and by a name (`m >> n`); the index is refused.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_bit.gen

namespace Examples.«system-verilog».gen_bit.comb_errors

/--
error: sv_structure: outside the supported fragment — conditional generate inside a generate loop: the condition is outside the v1 fragment (a signed comparison `s< s<= s> s>=`, or `==`, `!=`, of two affine forms in the parameters and the enclosing genvars: integer literals, `+`, `-`, `*` by a constant, the atoms `1 << n`, `b ** n`, `m >> n`, `(m >> n) << n`, `(m >> n) & 1` of names `m`, `n`, and `c ? x : y` of such forms under such a comparison `c`)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483647) : CombDesign (gen_bit_two.sem N) := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — site `g_node#0`: non-affine genvar-index obligation: read `a[…]` has a dynamic or nonlinear index, so the driven window cannot be determined
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483647) : CombDesign (gen_bit_sum.sem N) := by
  sv_structure

end Examples.«system-verilog».gen_bit.comb_errors
