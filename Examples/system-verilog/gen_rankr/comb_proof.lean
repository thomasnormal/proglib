import Examples.«system-verilog».gen_rankr.gen
import LeanModels.Sv.CombViewTactic

/-!
# `sv_structure` with the ranged rank obligations (`Examples/system-verilog/gen_rankr`, tac8)

`set_option sv_comb.rank_ranged true` states each rank obligation with the in-range facts of the read window and of the
written window as premises (`Summary.rankObl'_of_groupsR`, CombViewGroup.lean): those facts are the `auto` and
`inRange` obligations of the same theorem, proved once (here by `sv_pow_omega`, which states the facts of the products
`t*(P >> j)`); in a rank goal they put the columns of the two row-major windows inside their rows, so
`sv_rowmajor; omega` closes it without any fact about the products. In `gen_rankr_acyclic` the `auto` and `inRange`
obligations come from the `SharedObl` hypothesis, so every goal left is a rank goal, and each closes by exactly
`intros; sv_rowmajor; omega`.

Build: `lake build Examples.«system-verilog».gen_rankr.comb_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_rankr.gen

namespace Examples.«system-verilog».gen_rankr.comb_proof

set_option maxHeartbeats 1000000 in
/-- The structure of `gen_rankr`, at every `1 ≤ N < 2^29`. -/
theorem gen_rankr_comb (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 29) :
    CombDesign (gen_rankr.sem N) ∧ SharedObl gen_rankr.pdesign [N] := by
  sv_structure
  all_goals (intros; first | omega | (sv_rowmajor; omega) | sv_pow_omega | (sv_pow_facts; sv_rowmajor; omega))

set_option sv_comb.rank_ranged true in
/-- **The rank in the ranged form**: level `l` before level `l + 1`; every rank goal closes by `sv_rowmajor; omega`
from its premises (the in-range facts of its two windows). -/
theorem gen_rankr_acyclic (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 29) (hc : CombDesign (gen_rankr.sem N))
    (hso : SharedObl gen_rankr.pdesign [N]) : Acyclic (gen_rankr.sem N) := by
  sv_structure (lexRank := fun
    | .fam "g_t" _ [l, _, _] => (l.toNat + 1, 0, 0)
    | .plain 1 => (4, 0, 0)
    | _ => (0, 0, 0)) using hc
  all_goals (intros; sv_rowmajor; omega)

set_option maxHeartbeats 1000000 in
/-- The bundle `CombDesign ∧ Acyclic` in the ranged form. -/
theorem gen_rankr_struct (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 29) :
    CombDesign (gen_rankr.sem N) ∧ Acyclic (gen_rankr.sem N) := by
  set_option sv_comb.rank_ranged true in
  sv_structure (lexRank := fun
    | .fam "g_t" _ [l, _, _] => (l.toNat + 1, 0, 0)
    | .plain 1 => (4, 0, 0)
    | _ => (0, 0, 0))
  all_goals (intros; first | omega | (sv_rowmajor; omega) | sv_pow_omega | (sv_pow_facts; sv_rowmajor; omega))

/--
info: 'Examples.«system-verilog».gen_rankr.comb_proof.gen_rankr_acyclic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_rankr_acyclic

end Examples.«system-verilog».gen_rankr.comb_proof
