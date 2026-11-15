import Examples.«system-verilog».gen_clog2q.gen
import LeanModels.Sv.CombViewTactic

/-!
# `$clog2` of a quotient: what stays out (`Examples/system-verilog/gen_clog2q/neg`)

* `gen_clog2q_neg`: `NI = $clog2((N - 20) / 8) + 1`. At `N ≤ 12` the argument is `-2` or `-1` (`/` truncates toward
  zero, IEEE 1800-2023 §11.4.2), which `$clog2` reads as unsigned (§20.8.1): the instantiation's `NI` is `33` there, as
  Icarus prints it (`gen.lean`). The summary reads `$clog2` of a negative argument as `clog2 0` (`Int.toNat`), so its
  value of `NI` is `1` there: the two disagree and `sv_structure` refuses, naming both values (at `N = 5`). Under
  `13 ≤ N` the quotient is `0` or more (the facts of `Int.tdiv` by a literal, `tdiv_spec_of_pos`) and the design is
  proved.
* `gen_clog2q_div`: `$clog2((N + 9) / D)`, a quotient by a parameter: the recognizer refuses it (a localparam divides by
  an integer literal).
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_clog2q.gen

namespace Examples.«system-verilog».gen_clog2q.comb_errors

/--
error: sv_structure: the parameter values could not be read off the instantiation environment: the localparam `NI` is the 32-bit `int` 33 in the instantiation, and the summary's value of its definition is 1: the two readings differ at no operation the tactics can name
-/
#guard_msgs (whitespace := lax) in
example : CombDesign (gen_clog2q_neg.sem 5) := by
  sv_structure

/-- Under `13 ≤ N` the argument is `0` or more, where the summary's reading is the instantiation's: proved. -/
theorem gen_clog2q_neg_comb (N : Nat) (hN : 13 ≤ N) (hR : N < 2 ^ 20) : CombDesign (gen_clog2q_neg.sem N) := by
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
