import LeanModels.Sv.Ingest2

namespace Examples.«system-verilog».sem2.package_walls_h1

open LeanModels.Sv

load_design_sv2 h1 from "Examples/system-verilog/sem2/package_walls_h1/h1.json"

#guard h1.pdesign.packageParams.map (fun (_, p) => p.resolved?) ==
  [some 655372, some 589835, some 1, some 655372]
#guard h1.pdesign.defaultArgs == .ok [4]
-- The four package constants are compared with those values (and `W`, `i`, `o`).
#guard h1.pdesign.crossCheckFull == ([], 7)
-- The function is kept as written: a declaration, two statements and a return.
#guard h1.pdesign.functions.map (fun f => (f.name, f.fromPackage, f.stmts.map (·.length))) ==
  [("rec::pick", true, some 4)]
-- `rec::R = pick(1)` is `R_FAST`: `{16'd10, 16'd12}`.
#guard (match bindPackageParams { int32 := true, functions := h1.pdesign.functions }
      h1.pdesign.packageParams with
    | .ok env => (env.packageFVal "rec" "R").map fun (v, w, _) => (v.toNat?, w)
    | _ => none) == some (some 655372, 32)

end Examples.«system-verilog».sem2.package_walls_h1
