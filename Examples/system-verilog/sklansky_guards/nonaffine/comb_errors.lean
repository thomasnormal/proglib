import Examples.«system-verilog».sklansky_guards.nonaffine.gen
import LeanModels.Sv.CombProcTactic
open LeanModels.Sv LeanModels.Sv.CombView
open Examples.«system-verilog».sklansky_guards.nonaffine.gen
namespace Examples.«system-verilog».sklansky_guards.nonaffine.comb_errors
/-- `a[(i >> 1) << 1]` (a shift of the genvar by a literal amount, IEEE 1800-2023 §11.4.10) was refused as a non-affine
index before; it is now the atom `shlK i 1`, owed in its range (`0 ≤ i < 2^31`), which a range premise provides. -/
theorem nonaffine_comb (N : Nat) (hN : 1 ≤ N) (hR : N < 2 ^ 30) : CombDesign (nonaffine.sem N) := by
  sv_structure
  all_goals (intros; first | omega | sv_pow_omega)

end Examples.«system-verilog».sklansky_guards.nonaffine.comb_errors
