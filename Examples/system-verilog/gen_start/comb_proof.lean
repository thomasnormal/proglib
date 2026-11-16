import Examples.«system-verilog».gen_start.gen
import LeanModels.Sv.CombViewTactic

/-!
# `sv_structure` on generate loops whose start is not an integer literal (`Examples/system-verilog/gen_start`)

A start's value is `Hdr.lo` in the obligations: the loop ranges are `lo ≤ i < bound` (`Hdr.Rng`), the fuel is owed for
`bound - lo` iterations (`AutoObl`), and a `?:` start normalizes to an `if-then-else` term like any conditional atom. The
one-iteration loop's genvar is pinned to its start by `omega` (the `if-then-else` term is one atom to it); `sv_ite_cases`
splits the conditions where a branch needs them.

Build: `lake build Examples.«system-verilog».gen_start.comb_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».gen_start.gen

namespace Examples.«system-verilog».gen_start.comb_proof

/-- The structure of `gen_start` and its rank (every site reads inputs only), at every `1 ≤ N < 2^20`. -/
theorem gen_start_struct (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20) :
    CombDesign (gen_start.sem N) ∧ Acyclic (gen_start.sem N) := by
  sv_structure (lexRank := fun _ => (0, 0, 0))
  all_goals (intros; first | omega | (sv_rowmajor; omega) | (sv_ite_cases <;> omega))

/--
info: 'Examples.«system-verilog».gen_start.comb_proof.gen_start_struct' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_start_struct

end Examples.«system-verilog».gen_start.comb_proof
