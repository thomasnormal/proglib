import Examples.«system-verilog».gen_repa.gen
import LeanModels.Sv.CombViewTactic

/-!
# `sv_structure` on a replication count with a shift atom (`Examples/system-verilog/gen_repa`)

The counts `P >> l` and `P - (P >> l)` of `{(P >> l){a[0]}}` and `{(P - (P >> l)){a[N-1]}}` hold the atom `shr P l`; its
range (`0 ≤ P < 2^31`, `0 ≤ l < 32`, `XAt.Ok`) is owed with the atoms of the accesses (`Summary.XObl`), the counts'
non-negativity by `InRangeObl`; the two slots of each row in range and disjoint. Everything closes by `omega` with the
facts of `sv_pow_omega`.

Build: `lake build Examples.«system-verilog».gen_repa.comb_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_repa.gen

namespace Examples.«system-verilog».gen_repa.comb_proof

/-- The structure of `gen_repa`, at every `1 ≤ N < 2^28` (`P = 4N` a 32-bit `int`). -/
theorem gen_repa_comb (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 28) :
    CombDesign (gen_repa.sem N) ∧ SharedObl gen_repa.pdesign [N] := by
  sv_structure
  all_goals (intros; first | omega | (sv_rowmajor; (try simp only [true_and]); omega) | sv_pow_omega |
    (sv_pow_facts; sv_rowmajor; (try simp only [true_and]); omega))

/-- Every site reads inputs only: any rank. -/
theorem gen_repa_acyclic (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 28) (hc : CombDesign (gen_repa.sem N))
    (hso : SharedObl gen_repa.pdesign [N]) : Acyclic (gen_repa.sem N) := by
  sv_structure (lexRank := fun _ => (0, 0, 0)) using hc
  all_goals (intros; first | omega | sv_pow_omega)

/--
info: 'Examples.«system-verilog».gen_repa.comb_proof.gen_repa_comb' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_repa_comb

end Examples.«system-verilog».gen_repa.comb_proof
