import Examples.«system-verilog».gen_d3.gen
import LeanModels.Sv.CombViewTactic

/-!
# `sv_structure` on a three-dimensional packed declaration (`Examples/system-verilog/gen_d3`)

`t`, `a`, `b`, `y` are 3-D; every access is a whole signal. The obligations close by `omega`.

Build: `lake build Examples.«system-verilog».gen_d3.comb_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_d3.gen

namespace Examples.«system-verilog».gen_d3.comb_proof

/-- The structure of `gen_d3` and its rank (`t` before `y`), at every `1 ≤ N < 2^20`. -/
theorem gen_d3_comb (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) :
    CombDesign (gen_d3.sem N) ∧ Acyclic (gen_d3.sem N) := by
  sv_structure (lexRank := fun
    | .plain 1 => (1, 0, 0)
    | _ => (0, 0, 0))
  all_goals (intros; first | omega | sv_pow_omega)

/--
info: 'Examples.«system-verilog».gen_d3.comb_proof.gen_d3_comb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_d3_comb

end Examples.«system-verilog».gen_d3.comb_proof
