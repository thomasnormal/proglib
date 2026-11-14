import Examples.«system-verilog».gen_shk.gen
import LeanModels.Sv.CombViewTactic

/-!
# `sv_structure` on shifts by a literal amount (`Examples/system-verilog/gen_shk`)

The index `(i >> 1) << 1` and the condition's `i >> 2` are the atoms `shlK i 1` and `shrK i 2`; their range
obligations (`0 ≤ i < 2^31`) and the in-range obligations of the reads (`i / 2 * 2 ≤ N - 1`, `i / 4 ≤ N - 1`) close by
`omega` (a division by a literal power of two).

Build: `lake build Examples.«system-verilog».gen_shk.comb_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_shk.gen

namespace Examples.«system-verilog».gen_shk.comb_proof

/-- The structure of `gen_shk`, at every `1 ≤ N < 2^30`. -/
theorem gen_shk_comb (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 30) :
    CombDesign (gen_shk.sem N) ∧ SharedObl gen_shk.pdesign [N] := by
  sv_structure
  all_goals (intros; first | omega | sv_pow_omega)

/-- Every site reads inputs only: any rank. -/
theorem gen_shk_acyclic (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 30) (hc : CombDesign (gen_shk.sem N))
    (hso : SharedObl gen_shk.pdesign [N]) : Acyclic (gen_shk.sem N) := by
  sv_structure (lexRank := fun _ => (0, 0, 0)) using hc
  all_goals (intros; first | omega | sv_pow_omega)

/--
info: 'Examples.«system-verilog».gen_shk.comb_proof.gen_shk_comb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_shk_comb

end Examples.«system-verilog».gen_shk.comb_proof
