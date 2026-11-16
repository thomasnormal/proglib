import Examples.«system-verilog».gen_terc.gen
import LeanModels.Sv.CombViewTactic

/-!
# `sv_structure` on `?:` in an index and a loop bound (`Examples/system-verilog/gen_terc`)

The conditional atoms normalize to `if-then-else` terms of the obligations; `sv_ite_cases` splits on their conditions,
and `omega` closes each branch.

Build: `lake build Examples.«system-verilog».gen_terc.comb_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_terc.gen

namespace Examples.«system-verilog».gen_terc.comb_proof

/-- The structure of `gen_terc` and its rank (every site reads inputs only), at every `1 ≤ N < 2^20`. -/
theorem gen_terc_struct (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) :
    CombDesign (gen_terc.sem N) ∧ Acyclic (gen_terc.sem N) := by
  sv_structure (lexRank := fun _ => (0, 0, 0))
  all_goals (intros; first | omega | (sv_ite_cases <;> omega))

/--
info: 'Examples.«system-verilog».gen_terc.comb_proof.gen_terc_struct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_terc_struct

end Examples.«system-verilog».gen_terc.comb_proof
