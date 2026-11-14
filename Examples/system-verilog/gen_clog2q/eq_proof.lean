import Examples.«system-verilog».gen_clog2q.gen
import LeanModels.Sv.CombEqTactic

/-!
# `sv_equations` with `$clog2` of a quotient in a generate condition (`Examples/system-verilog/gen_clog2q`)

The equations of `gen_clog2q` hold the localparam at the summary's value `clog2 ((N + 9) / 8) + 1` (the parameter stage
showed the instantiation's 32-bit value equal to it below `N < 2^20`): bit `i` of `q` is bit `i` of `a` where
`i < NI`, else `0`.

Build: `lake build Examples.«system-verilog».gen_clog2q.eq_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombEq
open Examples.«system-verilog».gen_clog2q.gen

namespace Examples.«system-verilog».gen_clog2q.eq_proof

/-- `gen_clog2q` in a settled state: `q` holds the low `clog2 ((N + 9) / 8) + 1` bits of `a`. -/
theorem gen_clog2q_q (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 20)
    (hc : CombDesign (gen_clog2q.sem N)) (ha : Acyclic (gen_clog2q.sem N))
    (st : SvState) (heqs : CombEqs (gen_clog2q.sem N) st) (hsh : StateShape (gen_clog2q.sem N) st)
    (x : BitVec N) (hA : SvState.lookup st "a" = some (LVec.ofBitVec x)) :
    ∀ i, i < N → st.boolAt "q" i = (decide (i < clog2 ((N + 9) / 8) + 1) && st.boolAt "a" i) := by
  sv_equations
  · intro i hi
    have hq : ((N : Int) + 9) / 8 = (((N + 9) / 8 : Nat) : Int) := by omega
    by_cases h : i < clog2 ((N + 9) / 8) + 1
    · rw [eq_q_g_bit_0 i hi (by rw [hq, Int.toNat_natCast]; omega), decide_eq_true h, Bool.true_and]
    · rw [eq_q_g_bit_1 i hi (by rw [hq, Int.toNat_natCast]; omega), decide_eq_false h, Bool.false_and]
  all_goals first
    | (intros; omega)
    | sv_pow_omega
    | sv_cover
    | (refine inKnown_ofBitVec hA ?_; omega)

/--
info: 'Examples.«system-verilog».gen_clog2q.eq_proof.gen_clog2q_q' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_clog2q_q

end Examples.«system-verilog».gen_clog2q.eq_proof
