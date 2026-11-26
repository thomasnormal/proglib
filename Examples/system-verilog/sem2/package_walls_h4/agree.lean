import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.package_walls_h4
open LeanModels.Sv

load_design_sv2 h4Fn from "Examples/system-verilog/sem2/package_walls_h4/h4_fn.json"
load_design_sv2 h4Expr from "Examples/system-verilog/sem2/package_walls_h4/h4_expr.json"

/-- The bits of the one package constant of a design, MSB first, with its width. -/
private def const (d : PDesign) (n : String) : Option (String × Nat) :=
  match bindPackageParams { int32 := true, functions := d.functions } d.packageParams with
  | .ok env => (env.packageFVal "rec" n).map fun (v, w, _) => (v.toBinString, w)
  | _ => none

private def bin (w n : Nat) : String := (LVec.ofNat w n).toBinString

-- `rec::P = pack2(7, 9)` and `rec::Q = (64'd7 << 32) | 64'd9`, at 64 bits.
#guard const h4Fn.pdesign "P" == some (bin 32 7 ++ bin 32 9, 64)
#guard const h4Expr.pdesign "Q" == some (bin 32 7 ++ bin 32 9, 64)
-- The loader compares both with the parser's own value (30064771081).
#guard h4Fn.pdesign.packageParams.map (fun (_, p) => p.resolved?) == [some 30064771081]
#guard h4Fn.pdesign.crossCheckFull == ([], 2)
#guard h4Expr.pdesign.crossCheckFull == ([], 2)
-- `assign o = rec::P[63:32]`: the instantiated design reads 7.
private def reads7 (ps : List Process2) : Bool :=
  match ps with
  | [.assign (.ident "o") (.lit v)] => v == LVec.ofNat 32 7
  | [.assign (.ident "o") (.resize 32 (.lit v))] => v == LVec.ofNat 32 7
  | _ => false
#guard reads7 h4Fn.sem.processes.toList
#guard reads7 h4Expr.sem.processes.toList
end Examples.«system-verilog».sem2.package_walls_h4
