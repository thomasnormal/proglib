import Examples.«system-verilog».gen_repw.gen
import LeanModels.Sv.CombViewTactic

/-!
# `sv_structure` on replications of a whole signal (`Examples/system-verilog/gen_repw`, tac8)

The window of `{(P >> l){cin}}` is `P >> l` copies of the declared width of `cin`; its count's atom is owed in range by
`Summary.XObl`, its non-negativity by `InRangeObl` (tac7), and the facts of the shift atoms close the slots (`sv_pow_omega`).

Build: `lake build Examples.«system-verilog».gen_repw.comb_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_repw.gen

namespace Examples.«system-verilog».gen_repw.comb_proof

set_option maxHeartbeats 1000000 in
/-- The structure and the rank (`g` before `y0`, `y1`), at every `1 ≤ N < 2^28` (`P = 4N` a 32-bit `int`). -/
theorem gen_repw_struct (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 28) :
    CombDesign (gen_repw.sem N) ∧ Acyclic (gen_repw.sem N) := by
  sv_structure (lexRank := fun
    | .fam "g_lvl" _ _ => (0, 0, 0)
    | .plain 0 => (0, 0, 0)
    | _ => (1, 0, 0))
  -- the level-`l` write `g[l][0 +: (P >> l)]` against `g[1][P-1 -: (P >> 1)]`: disjoint rows at `l = 0`, the two halves
  -- of row 1 at `l = 1` (the loop has two iterations; `P >> l` is the atom `4N / 2^l`)
  case driverDisjoint_1 =>
    intro i h0 h1
    obtain rfl | rfl : i = 0 ∨ i = 1 := by omega
    · rw [show (2 : Int) ^ (0 : Int).toNat = 1 by decide]
      sv_rowmajor
      omega
    · rw [show (2 : Int) ^ (1 : Int).toNat = 2 by decide]
      sv_rowmajor
      omega
  all_goals (intros; first | omega | (sv_rowmajor; (try simp only [true_and]); omega) | sv_pow_omega |
    (sv_pow_facts; sv_rowmajor; (try simp only [true_and]); omega))

/--
info: 'Examples.«system-verilog».gen_repw.comb_proof.gen_repw_struct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_repw_struct

end Examples.«system-verilog».gen_repw.comb_proof
