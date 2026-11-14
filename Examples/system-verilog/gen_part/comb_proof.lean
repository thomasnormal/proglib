import Examples.«system-verilog».gen_part.gen
import LeanModels.Sv.CombViewTactic

/-!
# `sv_structure` on indexed part selects (`Examples/system-verilog/gen_part`)

Every `+:`/`-:` select of `gen_part.sv` is read as the range part with the bounds `partRange` gives, so the obligations
are the ones a range part select has: each window inside its row or vector (`0 ≤ lsb ≤ msb < width`, here
`2i ≤ 2i + 1 < 2N`), the windows of distinct instances disjoint, and the rank.

Build: `lake build Examples.«system-verilog».gen_part.comb_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_part.gen

namespace Examples.«system-verilog».gen_part.comb_proof

/-- The structure of `gen_part`, at every `1 ≤ N < 2^30`. -/
theorem gen_part_comb (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 30) :
    CombDesign (gen_part.sem N) ∧ SharedObl gen_part.pdesign [N] := by
  sv_structure
  all_goals (intros; first
    | omega
    | (sv_rowmajor; (try simp only [true_and]); omega))

/-- The rank: the rows of `g`, then `w`, then `y` and `z`. -/
theorem gen_part_acyclic (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 30) (hc : CombDesign (gen_part.sem N))
    (hso : SharedObl gen_part.pdesign [N]) : Acyclic (gen_part.sem N) := by
  sv_structure (lexRank := fun
    | .fam "g_node" _ _ => (0, 0, 0)
    | .fam "g_out" 0 _ => (1, 0, 0)
    | _ => (2, 0, 0)) using hc
  all_goals (intros; first
    | omega
    | (sv_rowmajor; (try simp only [true_and]); omega))

/--
info: 'Examples.«system-verilog».gen_part.comb_proof.gen_part_comb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_part_comb

/--
info: 'Examples.«system-verilog».gen_part.comb_proof.gen_part_acyclic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_part_acyclic

end Examples.«system-verilog».gen_part.comb_proof
