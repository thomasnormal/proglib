import Examples.«system-verilog».gen_clog2q.gen
import LeanModels.Sv.CombViewTactic

/-!
# `sv_structure` on `$clog2` of a quotient and a power of it (`Examples/system-verilog/gen_clog2q`)

The parameter stage evaluates `NI = $clog2((N + 9) / 8) + 1`, `L = $clog2((N + 3) / 4)` and `T = 3 ** L` at a symbolic
`N`: the instantiation's unsigned reading of each `$clog2` argument (IEEE 1800-2023 §20.8.1: modulo `2^32`) is the
argument where `omega` places it in `[0, 2^32)` from the range premise, each 32-bit wrap is removed where `omega` places
its value in range (the facts of `$clog2` atoms bound `T` through `3 ^ L ≤ 3 ^ 14` below `N < 2^16`), and the
environment it computes is the summary's valuation. Nothing is assumed: the range premises are the theorems'
hypotheses.

Build: `lake build Examples.«system-verilog».gen_clog2q.comb_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_clog2q.gen

namespace Examples.«system-verilog».gen_clog2q.comb_proof

/-- The structure of `gen_clog2q` at every `1 ≤ N < 2^20`. -/
theorem gen_clog2q_comb (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) :
    CombDesign (gen_clog2q.sem N) ∧ SharedObl gen_clog2q.pdesign [N] := by
  sv_structure
  all_goals (intros; first
    | omega
    | (sv_rowmajor; (try simp only [true_and]); omega)
    | sv_pow_omega)

/-- Every site of `gen_clog2q` reads inputs only: any rank. -/
theorem gen_clog2q_acyclic (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) (hc : CombDesign (gen_clog2q.sem N))
    (hso : SharedObl gen_clog2q.pdesign [N]) : Acyclic (gen_clog2q.sem N) := by
  sv_structure (lexRank := fun _ => (0, 0, 0)) using hc
  all_goals (intros; first
    | omega
    | (sv_rowmajor; (try simp only [true_and]); omega)
    | sv_pow_omega)

/-- The structure of `gen_ktree` at every `1 ≤ N < 2^16` (`T = 3 ^ L ≤ 3 ^ 14`, within the generate fuel). -/
theorem gen_ktree_comb (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 16) :
    CombDesign (gen_ktree.sem N) ∧ SharedObl gen_ktree.pdesign [N] := by
  sv_structure
  all_goals (intros; first
    | omega
    | (sv_rowmajor; (try simp only [true_and]); omega)
    | (sv_pow_facts <;> first | omega | (sv_rowmajor; (try simp only [true_and]); omega)))

/-- The rank of `gen_ktree`: the leaves, then the levels from the deepest up, then the output. -/
theorem gen_ktree_acyclic (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 16) (hc : CombDesign (gen_ktree.sem N))
    (hso : SharedObl gen_ktree.pdesign [N]) : Acyclic (gen_ktree.sem N) := by
  sv_structure (lexRank := fun
    | .fam "g_node" _ [l, _] => (40 - l.toNat, 0, 0)
    | .plain _ => (41, 0, 0)
    | _ => (0, 0, 0)) using hc
  all_goals (intros; first
    | omega
    | (sv_rowmajor; (try simp only [true_and]); omega)
    | (sv_pow_facts <;> first | omega | (sv_rowmajor; (try simp only [true_and]); omega)))

/--
info: 'Examples.«system-verilog».gen_clog2q.comb_proof.gen_clog2q_comb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_clog2q_comb

/--
info: 'Examples.«system-verilog».gen_clog2q.comb_proof.gen_ktree_acyclic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_ktree_acyclic

end Examples.«system-verilog».gen_clog2q.comb_proof
