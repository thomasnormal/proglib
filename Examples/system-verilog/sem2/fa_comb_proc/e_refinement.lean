import LeanModels.Sv.CombSlotE
import LeanModels.Sv.Comb2ProcExample

namespace Examples.«system-verilog».sem2.fa_comb_proc.e_refinement

open LeanModels.Sv LeanModels.Sv.Kernel LeanModels.Sv.Loop2
open LeanModels.Sv.Comb2ProcExample

def faW : List String := ["t", "s", "cout"]

theorem fa_equation_refines_E :
    SingleE (Elab.ofDesign2 faDesign) faBody (CombInv faDesign)
      (Stmt2.sem faDesign faBody) faW := by
  apply singleE_comb (d := faDesign) (body := faBody) (W := faW) rfl
  · intro dc hdc
    simp [Elab.ofDesign2, faDesign] at hdc
    rcases hdc with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · decide
  · decide
  · decide
  · decide
  · simp [faW, faDesign, Design2.inputNames]
  · intro st hst
    simp [faBody, Stmt2.listClaims, Stmt2.claims, Stmt2.optClaims]

#print axioms fa_equation_refines_E

end Examples.«system-verilog».sem2.fa_comb_proc.e_refinement
