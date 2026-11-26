/- Constant functions, casts and signed package constants: the rows of the
   repair round (`oracle_xcelium.txt`, `oracle_iverilog.txt`; the two agree
   on every row).  Each row is a value the loader once got wrong without a
   refusal. -/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleStages
import LeanModels.Sv.Sem2Run
import LeanModels.Sv.RangeGuard2
namespace Examples.«system-verilog».sem2.package_const_repairs.agree
open LeanModels.Sv LeanModels.Sv.Kernel

load_design_sv2 pcrLeaf from
  "Examples/system-verilog/sem2/package_const_repairs/pcr_leaf.sv.json"
load_design_sv2 pcrGen from
  "Examples/system-verilog/sem2/package_const_repairs/pcr_gen.sv.json"
load_design_sv2 pcrUnset from
  "Examples/system-verilog/sem2/package_const_repairs/pcr_unset.sv.json"

/-- A bound package constant: bits (MSB first), width, signedness. -/
private def const (d : PDesign) (pkg n : String) : Option (String × Nat × Bool) :=
  match bindPackageParams { int32 := true, functions := d.functions } d.packageParams with
  | .ok env => (env.packageFVal pkg n).map fun (v, w, s) => (v.toBinString, w, s)
  | _ => none

private def bin (w : Nat) (v : Int) : String := (LVec.ofInt w v).toBinString

/-! The loader's differential, which now compares every package constant bit
for bit (x and z included) with its width and signedness. -/
#guard pcrLeaf.pdesign.crossCheckFull.1 == []
#guard pcrGen.pdesign.crossCheckFull.1 == []
#guard pcrUnset.pdesign.crossCheckFull.1 == []
#guard pcrLeaf.pdesign.packageParams.all fun (_, p) => p.resolvedBits?.isSome

/-! `CONST` rows.  Selects of function variables whose range is not `[m:0]`
(`PX`, `RES`), explicit casts (`CX`, `CA`, `CD`), signed constants typed and
untyped (`M`, `MU`), a static function in a constant call (`TS`). -/
#guard const pcrLeaf.pdesign "pcr" "PX" == some ("1x", 2, false)
#guard const pcrLeaf.pdesign "pcr" "RES" == some ("100x", 4, false)
#guard const pcrLeaf.pdesign "pcr" "CX" == some ("x00001011", 9, false)
#guard const pcrLeaf.pdesign "pcr" "CA" == some ("0000000000001011", 16, false)
#guard const pcrLeaf.pdesign "pcr" "CD" == some ("00001100", 8, false)
#guard const pcrLeaf.pdesign "pcr" "M" == some (bin 32 (-3), 32, true)
#guard const pcrLeaf.pdesign "pcr" "MU" == some (bin 32 (-3), 32, true)
#guard const pcrLeaf.pdesign "pcr" "TS" == some (bin 32 42, 32, true)
-- The function is static in the source, and the envelope says so.
#guard (pcrLeaf.pdesign.functions.filter (·.name == "pcr::twice_static")).map (·.automatic) == [false]

/-- The module's constants at a parameter point, through the canonical E
instantiation: name, bits, width, signedness. -/
private def consts (pt : List (Option Int)) : List (String × String × Nat × Bool) :=
  match pcrLeaf.pdesign.atPoint pt with
  | .error _ => []
  | .ok (pd, args) =>
      match LeanModels.Sv.Kernel.PDesign.instantiateE2 pd args (PDesign.surfaceFuel args) with
      | .ok E =>
          (E.env.nvals.map fun (n, (v, w, s)) => (n, bin w v, w, s)) ++
            E.env.vals.map fun (n, v) => (n, bin 32 v, 32, true)
      | _ => []

private def valAt (pt : List (Option Int)) (n : String) : Option String :=
  ((consts pt).find? (·.1 == n)).map (·.2.1)

/-! `POINT default` row: `N = 8'h81`, `Q = 0`. -/
#guard valAt [] "L1" == some "1"
#guard valAt [] "L2" == some "1"
#guard valAt [] "L3" == some "1"
#guard valAt [] "L4" == some "1000"
#guard valAt [] "L5" == some "00000001"
#guard valAt [] "U1" == some (bin 32 0)
#guard valAt [] "U2" == some (bin 32 0)

/-! `POINT N=80,Q=2` row.  At `N = 8'h80` the most significant bit is the only
one set, so a select that reads the wrong end gives 0 (the default point
cannot tell: `8'h81` has both ends set).  `U1 = pcr::M >>> 1 = -2` and
`U2 = pcr::MU / 2 = -1`: the package constants are signed. -/
#guard valAt [some 128, some 2] "L1" == some "1"
#guard valAt [some 128, some 2] "L2" == some "1"
#guard valAt [some 128, some 2] "L3" == some "1"
#guard valAt [some 128, some 2] "L4" == some "1000"
#guard valAt [some 128, some 2] "L5" == some "00000000"
#guard valAt [some 128, some 2] "U1" == some (bin 32 (-2))
#guard valAt [some 128, some 2] "U2" == some (bin 32 (-1))

/-! `G 2` in both `POINT` rows: the module function `addk` reads the module's
`K = 1`, although the generate block that calls it declares `K = 100`. -/
private def genG (r : Res CoreMemDesign) : List Int :=
  match r with
  | .ok E => E.processes.toList.filterMap fun p =>
      match p with
      | .assign (.ident "o_g") (.int v) => some v
      | _ => none
  | _ => []
#guard genG (pcrLeaf.e 129 0) == [2]
#guard genG (pcrLeaf.e 128 2) == [2]

/-! `GEN o 00000111`: the genvar starts at the signed package constant
`pcr::M = -3` and the loop runs three times (it used to start at 4294967293
and run zero times). -/
private def genIters (r : Res CoreMemDesign) : List Int :=
  match r with
  | .ok E => E.processes.toList.filterMap fun p =>
      match p with
      | .assign (.bitSel "o" (.binary _ (.int g) (.int 3))) _ => some g
      | _ => none
  | _ => []
#guard genIters pcrGen.e == [-3, -2, -1]

/-! A four-state function result that is never assigned is x (IEEE 1800-2023
§6.8, §13.4.3).  Xcelium folds 0 at elaboration and gives x at run time; no
oracle result is claimed for the elaboration value. -/
#guard const pcrUnset.pdesign "pcr_u" "UNSET" == some ("xxxx", 4, false)

end Examples.«system-verilog».sem2.package_const_repairs.agree
