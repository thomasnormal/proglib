import Examples.«system-verilog».gen_tercg.gen
import LeanModels.Sv.CombViewTactic

/-!
# `sv_structure` on `?:` operands of generate-if conditions (`Examples/system-verilog/gen_tercg`)

A guard with a conditional atom normalizes to a comparison with an `if-then-else` operand; `sv_ite_cases` splits on its
condition, and `omega` closes each branch (the two arms of each `if` write the same bit under complementary guards).

Build: `lake build Examples.«system-verilog».gen_tercg.comb_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_tercg.gen

namespace Examples.«system-verilog».gen_tercg.comb_proof

/-- The structure of `gen_tercg` and its rank (every site reads inputs only), at every `1 ≤ N < 2^20`. -/
theorem gen_tercg_struct (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) :
    CombDesign (gen_tercg.sem N) ∧ Acyclic (gen_tercg.sem N) := by
  sv_structure (lexRank := fun _ => (0, 0, 0))
  all_goals (intros; first | omega | (sv_ite_cases <;> omega))

/--
info: 'Examples.«system-verilog».gen_tercg.comb_proof.gen_tercg_struct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_tercg_struct

end Examples.«system-verilog».gen_tercg.comb_proof
