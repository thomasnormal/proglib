import Examples.«system-verilog».gen_d3s.gen
import LeanModels.Sv.CombViewTactic

/-!
# `sv_structure` on the selects of a three-dimensional array (`Examples/system-verilog/gen_d3s`, tac8)

Every window is a nested row-major offset `rmN 4 (rmN 3 s k) c` of `T` or `U`. `sv_rowmajor` compares two of them
lexicographically, first by the outer offset (`rmN_lt_iff`, the row `rmN 3 s k` against the row), then the rows by the
inner offset (`rmN_cast_lt_iff`, `rmN_cast_eq_iff`), and the end of the plane `T[0]` as the start of plane 1
(`rmN3_plane_end_k`); `omega` closes what is left. The rank is in the ranged form (`sv_comb.rank_ranged`): every rank
goal closes from its own premises.

Build: `lake build Examples.«system-verilog».gen_d3s.comb_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_d3s.gen

namespace Examples.«system-verilog».gen_d3s.comb_proof

/-- The structure of `gen_d3s`, at every `1 ≤ N < 2^20`. -/
theorem gen_d3s_comb (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) :
    CombDesign (gen_d3s.sem N) ∧ SharedObl gen_d3s.pdesign [N] := by
  sv_structure
  all_goals (intros; first | omega | (sv_rowmajor; (try simp only [true_and]); omega))

set_option sv_comb.rank_ranged true in
/-- The rank: the plane `T[0]`, then plane by plane the rows of `T` and the parts of `U`, the outputs last. -/
theorem gen_d3s_acyclic (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) (hc : CombDesign (gen_d3s.sem N))
    (hso : SharedObl gen_d3s.pdesign [N]) : Acyclic (gen_d3s.sem N) := by
  sv_structure (lexRank := fun
    | .plain 0 => (0, 0, 0)
    | .fam "g_row" _ [s, _] => (1, s.toNat, 0)
    | .fam "g_part" _ [s, _] => (1, s.toNat, 1)
    | _ => (2, 0, 0)) using hc
  all_goals (intros; sv_rowmajor; (try simp only [true_and]); omega)

/-- `gen_d3p`: whole planes over a parameter middle dimension, and a cell (the structure and the rank). -/
theorem gen_d3p_struct (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) :
    CombDesign (gen_d3p.sem N) ∧ Acyclic (gen_d3p.sem N) := by
  sv_structure (lexRank := fun
    | .plain 0 => (0, 0, 0)
    | .plain 1 => (1, 0, 0)
    | _ => (2, 0, 0))
  all_goals (intros; first | omega | (sv_rowmajor; (try simp only [true_and]); omega))

/--
info: 'Examples.«system-verilog».gen_d3s.comb_proof.gen_d3s_acyclic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_d3s_acyclic

end Examples.«system-verilog».gen_d3s.comb_proof
