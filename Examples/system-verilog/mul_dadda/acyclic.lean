import Examples.«system-verilog».mul_dadda.comb_proof

/-!
# The Dadda record has no combinational loop, at every `1 ≤ N < 2^30` (`Examples/system-verilog/mul_dadda`)

`mul_dadda_struct : CombDesign (mul_dadda.sem N) ∧ Acyclic (mul_dadda.sem N)`: the rank obligations of `sv_structure`
(the ranged form, so the in-range facts come from `SharedObl`, proved with the profile in `comb_proof.lean`), each closed
by the same closer (`dadda_close`). A file of its own: with both theorems in one file the build passed 8 GB.

Build: `lake build Examples.«system-verilog».mul_dadda.acyclic`.
-/

open Lean Elab Tactic Meta
open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».mul_dadda.gen Examples.«system-verilog».mul_dadda.comb_proof

namespace Examples.«system-verilog».mul_dadda.acyclic

set_option sv_comb.lp_atoms true in
set_option sv_comb.auto_close false in
set_option sv_comb.rank_ranged true in
set_option maxHeartbeats 40000000 in
/-- **No combinational loop**: partial products first, then stage `s`'s adders (key `2s + 1`) and stage `s`'s next
columns (key `2s + 2`), then the final ripple-carry adder column by column. The in-range obligations come from `hso`. -/
theorem mul_dadda_acyclic (N : Nat) (hN : 1 ≤ N) (h30 : N < 2 ^ 30) (hc : CombDesign (mul_dadda.sem N))
    (hso : SharedObl mul_dadda.pdesign [N]) : Acyclic (mul_dadda.sem N) := by
  quiet sv_structure (lexRank := fun
    | .fam "g_add" _ (s :: _) => (1, 2 * s.toNat + 1, 0)
    | .fam "g_st.g_t.g_u.g_col.g_f.g_h.g_c.g_bit" _ (s :: _) => (1, 2 * s.toNat + 2, 0)
    | .fam "g_fin" 0 [k] => (2, k.toNat, 1)
    | .fam "g_fin" _ [k] => (2, k.toNat, 0)
    | _ => (0, 0, 0)) using hc
  all_goals dadda_close

/-- **The Dadda record's structure at every `1 ≤ N < 2^30`**: the combinational profile and no combinational loop. -/
theorem mul_dadda_struct (N : Nat) (hN : 1 ≤ N) (h30 : N < 2 ^ 30) :
    CombDesign (mul_dadda.sem N) ∧ Acyclic (mul_dadda.sem N) :=
  ⟨(mul_dadda_comb_shared N hN h30).1,
    mul_dadda_acyclic N hN h30 (mul_dadda_comb_shared N hN h30).1 (mul_dadda_comb_shared N hN h30).2⟩

/--
info: 'Examples.«system-verilog».mul_dadda.acyclic.mul_dadda_struct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms mul_dadda_struct

end Examples.«system-verilog».mul_dadda.acyclic
