import Examples.«system-verilog».clmul_kara.gen
import LeanModels.Sv.CombTaskTactic

/-!
# The 27 obligations of the Karatsuba record's equations, closed by `sv_obligations`

`sv_equations` on the record (`clmul_kara.sv`, every index a genvar times a slot width `P >> l`) states, besides the
settled-state equations, 27 obligations: 9 width, 16 coverage and 2 input-knowledge goals. The coverage goals say that
every bit a read observes has a writer: their witnesses are quotients and multiples of the reader's genvars (the writer
of a split node's operand is node `t / 3` of the level above, piece `t % 3`; the writer of a combine node's product is
node `3·t + c` of the level below, or the base), and their windows compare products of a genvar with a symbolic slot
width. `sv_cover`'s slot-window rule (`LeanModels/Sv/CombCoverUnit.lean`) solves those witnesses from the writers' index
maps and states the facts of the slot widths (`P >> l = 4·2^L / 2^l`) itself; `sv_obligations` closes all 27.

The theorem states a trivial specification: the point is the obligations `sv_equations` hands back (the carry-less
product is proved in `clmul_proof.lean`, the full statement). The structure (`CombDesign`, `Acyclic`, the shared
obligations) is a hypothesis.

The range premise `N < 2^16` is the record's own: `T = 3^L` is a 32-bit `int`, and `4·T` must stay in range.

Build: `lake build Examples.«system-verilog».clmul_kara.cover`.
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombEq
open Examples.«system-verilog».clmul_kara.gen

namespace Examples.«system-verilog».clmul_kara.cover

set_option sv_comb.lp_atoms true in
set_option maxHeartbeats 4000000 in
/-- Every obligation of `sv_equations` on the record (27: width, coverage, input knowledge) closes by `sv_obligations`. -/
theorem kara_obligations (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 16)
    (hc : CombDesign (clmul_kara.sem N)) (ha : Acyclic (clmul_kara.sem N))
    (hso : SharedObl clmul_kara.pdesign [N]) :
    clmul_kara.sem N ⊨₂ spec2 fun _ tr => ∀ (c : Nat) (st : SvState), tr[c]? = some st →
      ∀ (x y : BitVec N),
        SvState.lookup st "a" = some (LVec.ofBitVec x) →
        SvState.lookup st "b" = some (LVec.ofBitVec y) → True := by
  refine Models2.of_comb_pointwise hc (fun st heqs hsh => ?_)
  intro x y hA hB
  sv_equations
  · trivial
  sv_obligations

/-- info: 'Examples.«system-verilog».clmul_kara.cover.kara_obligations' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms kara_obligations

end Examples.«system-verilog».clmul_kara.cover
