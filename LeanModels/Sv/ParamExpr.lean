import Lean
import LeanModels.Sv.Param

namespace LeanModels.Sv

deriving instance Lean.ToExpr for PEventEdge
deriving instance Lean.ToExpr for PEvent
instance : Lean.ToExpr (List PEvent) where
  toExpr xs := xs.foldr
    (fun x acc => Lean.mkApp3 (Lean.mkConst ``List.cons [.zero])
      (Lean.ToExpr.toTypeExpr (α := PEvent)) (Lean.toExpr x) acc)
    (Lean.mkApp (Lean.mkConst ``List.nil [.zero]) (Lean.ToExpr.toTypeExpr (α := PEvent)))
  toTypeExpr := Lean.mkApp (Lean.mkConst ``List [.zero])
    (Lean.ToExpr.toTypeExpr (α := PEvent))

end LeanModels.Sv
