/- Typedef widths and shapes declared in packages, as the types of ports,
   variables, localparams and package constants (`oracle_xcelium.txt`,
   `oracle_iverilog.txt`: rows `BITS`, `PARAM`). -/
import LeanModels.Sv.Ingest2
namespace Examples.«system-verilog».sem2.package_typedef_shapes.agree
open LeanModels.Sv

load_design_sv2 ptsLeaf from
  "Examples/system-verilog/sem2/package_typedef_shapes/pts_leaf.sv.json"

/-! The loader's differential against the parser: the parameter, both
localparams, the width of every port and variable, and the package
constants. -/
#guard ptsLeaf.pdesign.crossCheckFull.1 == []
#guard ptsLeaf.pdesign.defaultArgs == .ok [2]
#guard ptsLeaf.pdesign.localParams.map (fun l => (l.name, l.resolved?)) ==
  [("K", some 5), ("K2", some 9)]

/-- Declared widths at a parameter point (`BITS` row at `P = 2`). -/
private def widths (p : Int) : List (String × Nat) :=
  let d := ptsLeaf.pdesign
  match bindPackageParams { functions := d.functions } d.packageParams with
  | .ok envP =>
      match bindParams envP d.params [p] with
      | .ok env0 =>
          match bindLocals env0 d.localParams with
          | .ok env1 =>
              d.decls.filterMap fun pd =>
                match pd.type.width env1 with
                | .ok w => some (pd.name, w)
                | .error _ => none
          | _ => []
      | _ => []
  | _ => []

#guard widths 2 ==
  [("a", 4), ("b", 4), ("c", 4), ("d", 6), ("e", 4), ("oa", 4), ("ob", 4), ("oc", 4), ("od", 6),
   ("oe", 4), ("op", 8), ("om", 3), ("v", 4), ("w", 6), ("mem", 3)]
-- The use-site dimension follows the module parameter; the typedef's own
-- dimension stays the package's.
#guard (widths 5).filter (fun x => x.1 == "b" || x.1 == "w" || x.1 == "a" || x.1 == "d") ==
  [("a", 4), ("b", 10), ("d", 6), ("w", 15)]

/-- Every dimension bound of a typedef-typed declaration that names a package
parameter carries the package: none is an unresolved identifier. -/
private def dimsOf (n : String) : Option (List PDim) :=
  (ptsLeaf.pdesign.decls.find? (·.name == n)).bind fun pd =>
    match pd.type with
    | .packed ds _ => some ds
    | _ => none
#guard dimsOf "a" ==
  some [⟨.binary (.m0 .sub) (.paramRef "SW" (some "pts_base")) (.int 1), .int 0⟩]
#guard (dimsOf "b").map (·.length) == some 2
#guard (dimsOf "d").map (·.length) == some 2
#guard (dimsOf "w").map (·.length) == some 2
-- The element of the unpacked array `mem [P]` keeps the typedef's own bound.
#guard dimsOf "mem" ==
  some [⟨.binary (.m0 .sub) (.paramRef "HW" (some "pts_base")) (.int 1), .int 0⟩]

/-! The package constants: one typed by a typedef chain, one a packed array
of packed structs (`PARAM ... SEL_INIT 9 PAIRS 01020304`). -/
#guard (match bindPackageParams { functions := ptsLeaf.pdesign.functions }
      ptsLeaf.pdesign.packageParams with
    | .ok env =>
        [(env.packageFVal "pts_cfg" "SEL_INIT").map (fun (v, w, _) => (v.toNat?, w)),
         (env.packageFVal "pts_cfg" "PAIRS").map (fun (v, w, _) => (v.toNat?, w))]
    | _ => []) == [some (some 9, 4), some (some 0x01020304, 32)]
#guard (match bindPackageEnums { int32 := true, functions := ptsLeaf.pdesign.functions }
      ptsLeaf.pdesign.enums with
    | .ok e => packageParamRefusals e ptsLeaf.pdesign.packageParams
    | _ => ["enums"]) == []

end Examples.«system-verilog».sem2.package_typedef_shapes.agree
