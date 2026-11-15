import Examples.«system-verilog».gen_pow.gen
import LeanModels.Sv.CombViewTactic

/-!
# Shifts outside the atoms, an atom in a declaration, and an atom's range obligation (`Examples/system-verilog/gen_pow/neg`)

* `gen_pow_two`: `(2 << l) - 2` in an index: `c << n` is an atom only for `c = 1` (`xatOf?`); refused, naming the index.
* `gen_pow_amt`: `1 << (l + 1)` in a condition: a shift by a sum is not an atom; refused, naming the guard fragment.
* `gen_pow_decl`: `1 << N` in a declared bound: the declarations stay atom-free (`dimOf?`); refused.
* `gen_pow_wide`: `(1 << l) > 0` for every `l < N`: read, but the atom `2 ^ l` is owed in its range at every `l`
  (`XAt.Ok`: `l < 32`, `2 ^ l < 2^31`): under `N < 2^31 - 1` alone that obligation is false at `l = 31`, where the
  instantiation, as IEEE's `int` does, wraps `1 << 31` to `-2^31` (`gen.lean`); under `N ≤ 31` it holds and the design
  is proved.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_pow.gen

namespace Examples.«system-verilog».gen_pow.comb_errors

/--
error: sv_structure: outside the supported fragment — site `g_lvl#0`: non-affine genvar-index obligation: read `a[…]` has a dynamic or nonlinear index, so the driven window cannot be determined
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483647) : CombDesign (gen_pow_two.sem N) := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — conditional generate inside a generate loop: the condition is outside the v1 fragment (a signed comparison `s< s<= s> s>=`, or `==`, `!=`, of two affine forms in the parameters and the enclosing genvars: integer literals, `+`, `-`, `*` by a constant, the atoms `1 << n`, `b ** n`, `m >> n`, `(m >> n) << n`, `(m >> n) & 1` of names `m`, `n`, and `c ? x : y` of such forms under such a comparison `c`)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483647) : CombDesign (gen_pow_amt.sem N) := by
  sv_structure

/--
error: sv_structure: outside the supported fragment — declaration `w`: a packed bound holds a shift or a power of a parameter (outside the fragment: name the value with a localparam)
-/
#guard_msgs (whitespace := lax) in
example (N : Nat) (hN : 1 ≤ N) (hR : (N : Int) < 2147483647) : CombDesign (gen_pow_decl.sem N) := by
  sv_structure

/-- The atom's range, at `l = 31`: false (`2 ^ 31` is no `int`), so under `N < 2^31 - 1` alone the obligation
`Summary.XObl` of `gen_pow_wide` (`∀ l < N, …`) cannot be closed. -/
example : ¬ (XAt.pow 2 "l").Ok (fun _ => 31) := by decide

/-- With `N ≤ 31` the atom is in range at every `l < N` and the design is proved. -/
theorem gen_pow_wide_comb (N : Nat) (hN : 1 ≤ N) (hR : N ≤ 31) : CombDesign (gen_pow_wide.sem N) := by
  sv_structure
  all_goals (intros; first | omega | sv_pow_omega)

/--
info: 'Examples.«system-verilog».gen_pow.comb_errors.gen_pow_wide_comb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_pow_wide_comb

end Examples.«system-verilog».gen_pow.comb_errors
