import Examples.«system-verilog».gen_lpat.gen
import LeanModels.Sv.CombViewTactic

/-!
# `sv_structure` with the localparams as variables (`Examples/system-verilog/gen_lpat`, tac9)

With `set_option sv_comb.lp_atoms true` every obligation reads the localparam `S` as a variable, its definition the
hypothesis `hlp_S : <the sum of `?:`> = S`; `sv_ite_omega` splits the conditions of that definition only where `omega`
needs them (`S ≤ N`, `0 ≤ S`: a branch that contradicts the context closes at once).

Build: `lake build Examples.«system-verilog».gen_lpat.comb_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_lpat.gen

namespace Examples.«system-verilog».gen_lpat.comb_proof

set_option sv_comb.lp_atoms true in
/-- The structure of `gen_lpat` and its rank (every site reads the input only), at every `1 ≤ N < 2^20`. -/
theorem gen_lpat_struct (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) :
    CombDesign (gen_lpat.sem N) ∧ Acyclic (gen_lpat.sem N) := by
  sv_structure (lexRank := fun _ => (0, 0, 0))
  all_goals (intros; sv_ite_omega)

/--
info: 'Examples.«system-verilog».gen_lpat.comb_proof.gen_lpat_struct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_lpat_struct

end Examples.«system-verilog».gen_lpat.comb_proof
