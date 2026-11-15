import Examples.«system-verilog».gen_clog2q.gen
import LeanModels.Sv.CombViewTactic

/-!
# `$clog2` of a quotient: a negative argument, and what stays out (`Examples/system-verilog/gen_clog2q/neg`)

* `gen_clog2q_neg`: `NI = $clog2((N - 20) / 8) + 1`. At `N ≤ 12` the argument is `-2` or `-1` (`/` truncates toward
  zero, IEEE 1800-2023 §11.4.2), which `$clog2` reads as unsigned (§20.8.1): `NI` is `33` there, in the instantiation
  as Icarus prints it, and in the summary, which reads the argument's 32-bit pattern (`% 2^32`) as the instantiation
  does (`gen.lean` pins both). It is no longer a refusal: the design is proved at every `1 ≤ N < 2^20`, and at a
  concrete `N ≤ 12`.
* `gen_clog2q_div`: `$clog2((N + 9) / D)`, a quotient by a parameter: the recognizer refuses it (a localparam divides by
  an integer literal).
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_clog2q.gen

namespace Examples.«system-verilog».gen_clog2q.comb_errors

/-- At every `1 ≤ N < 2^20`: at `N ≤ 12` the summary and the instantiation both read the negative quotient as unsigned
(`NI = 33`), above it as itself. -/
theorem gen_clog2q_neg_comb (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) : CombDesign (gen_clog2q_neg.sem N) := by
  sv_structure
  all_goals (intros; first | omega | sv_pow_omega)

/-- At `N = 5`, where the quotient is `-1`. -/
example : CombDesign (gen_clog2q_neg.sem 5) := by
  sv_structure
  all_goals (intros; first | omega | sv_pow_omega)

/--
error: sv_structure: outside the supported fragment — localparam `NI`: `/` by a non-literal is outside the v1 fragment (a localparam may divide by an integer literal)
-/
#guard_msgs (whitespace := lax) in
example (N D : Nat) (hN : 1 ≤ N) (hD : 1 ≤ D) (hR : N < 2 ^ 20) (hR2 : D < 2 ^ 20) :
    CombDesign (gen_clog2q_div.sem N D) := by
  sv_structure

/--
info: 'Examples.«system-verilog».gen_clog2q.comb_errors.gen_clog2q_neg_comb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_clog2q_neg_comb

end Examples.«system-verilog».gen_clog2q.comb_errors
