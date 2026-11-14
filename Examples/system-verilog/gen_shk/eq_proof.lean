import Examples.«system-verilog».gen_shk.gen
import LeanModels.Sv.CombEqTactic
import LeanModels.Sv.CombTaskTactic

/-!
# `sv_equations` with shifts by a literal amount (`Examples/system-verilog/gen_shk`)

The equations read `a[(i >> 1) << 1]` at the column `i / 2 * 2`, and the condition `(i >> 2) == 0` as `i / 4 = 0`
(`sv_eq_nat`: `Nat` indices).

Build: `lake build Examples.«system-verilog».gen_shk.eq_proof`.
-/

open LeanModels.Sv LeanModels.Sv.CombView LeanModels.Sv.CombEq
open Examples.«system-verilog».gen_shk.gen

namespace Examples.«system-verilog».gen_shk.eq_proof

/-- `gen_shk` in a settled state: `s[i] = a[i / 2 * 2] ^ b[i]`, and `t[i]` is `a[i]` for `i < 4`, else `b[i / 4]`. -/
theorem gen_shk_st (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 30)
    (hc : CombDesign (gen_shk.sem N)) (ha : Acyclic (gen_shk.sem N))
    (st : SvState) (heqs : CombEqs (gen_shk.sem N) st) (hsh : StateShape (gen_shk.sem N) st)
    (x y : BitVec N) (hA : SvState.lookup st "a" = some (LVec.ofBitVec x))
    (hB : SvState.lookup st "b" = some (LVec.ofBitVec y)) :
    ∀ i, i < N → st.boolAt "s" i = (st.boolAt "a" (i / 2 * 2) ^^ st.boolAt "b" i) ∧
      st.boolAt "t" i = (if i / 4 = 0 then st.boolAt "a" i else st.boolAt "b" (i / 4)) := by
  sv_equations
  · sv_eq_nat
    intro i hi
    refine ⟨eq_s_g_bit_0 i hi, ?_⟩
    split
    · next h => exact eq_t_g_bit_1 i hi h
    · next h => exact eq_t_g_bit_2 i hi h
  sv_obligations

/--
info: 'Examples.«system-verilog».gen_shk.eq_proof.gen_shk_st' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gen_shk_st

end Examples.«system-verilog».gen_shk.eq_proof
