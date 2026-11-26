/- Package constants, constant functions and typedef widths: one design whose
   every constant is compared with the reference simulator's own value
   (`oracle_xcelium.txt`, rows `CONST`/`HEX`/`PARAM`/`ROW`). -/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleStages
namespace Examples.«system-verilog».sem2.package_const_eval.agree
open LeanModels.Sv LeanModels.Sv.Kernel

load_design_sv2 pceLeaf from
  "Examples/system-verilog/sem2/package_const_eval/pce_leaf.sv.json"

private def pkgEnv (d : PDesign) : IEnv :=
  match bindPackageEnums { int32 := true, functions := d.functions } d.enums with
  | .ok e => (bindPackageParams e d.packageParams).toOption.getD {}
  | _ => {}

/-- A bound package constant: its bits (MSB first), width and signedness. -/
private def const (pkg n : String) : Option (String × Nat × Bool) :=
  ((pkgEnv pceLeaf.pdesign).packageFVal pkg n).map fun (v, w, s) => (v.toBinString, w, s)

private def bin (w n : Nat) : String := (LVec.ofNat w n).toBinString

/-! The loader's own differential: every `resolved` value the parser gives
(parameters, localparams, declared widths, generate counts and, since this
round, the package constants) agrees, and 37 values were compared. -/
#guard pceLeaf.pdesign.crossCheckFull == ([], 37)
#guard pceLeaf.pdesign.defaultArgs == .ok [4]
#guard pceLeaf.pdesign.localParams.map (fun l => (l.name, l.resolved?)) == [("K", some 8)]

/-! Widths 1, 32, 33, 64, 65 and 1088; signed and unsigned; x and z digits. -/
#guard const "pce_base" "B1" == some ("1", 1, false)
#guard const "pce_base" "NEG" == some ("11111111111111111111111111111101", 32, true)
#guard const "pce_base" "W32" == some ("11011110101011011011111011101111", 32, false)
#guard const "pce_base" "S32" == some ("11111111111111111111111111111110", 32, true)
#guard const "pce_base" "W33" == some ("100000000000000000000000000000001", 33, false)
#guard const "pce_base" "W64" ==
  some ("0000000000000000000000000000011100000000000000000000000000001001", 64, false)
#guard const "pce_base" "W65" ==
  some ("10000000000000000000000000000000000000000000000000000000000000011", 65, false)
#guard const "pce_base" "S65" ==
  some ("11111111111111111111111111111111111111111111111111111111111111011", 65, true)
#guard const "pce_base" "XZ8" == some ("1x0z01zx", 8, false)
#guard const "pce_base" "PAIR" == some (bin 32 7 ++ bin 32 9, 64, false)
#guard const "pce_base" "WIDE" == some (bin 1024 0 ++ bin 32 10 ++ bin 32 12, 1088, false)
#guard const "pce_base" "WX" == some ("1x0z01zx" ++ bin 1080 5, 1088, false)

/-! A second package: aliases of the first, nested calls, procedural bodies. -/
#guard const "pce_cfg" "UNITS" == some (bin 32 4, 32, false)
#guard const "pce_cfg" "UNIT_W" == some (bin 32 2, 32, false)
#guard const "pce_cfg" "M3" == some (bin 32 6, 32, false)
#guard const "pce_cfg" "POW2" == some ("1", 1, false)
#guard const "pce_cfg" "PICK1" == some (bin 1024 0 ++ bin 32 10 ++ bin 32 12, 1088, false)
#guard const "pce_cfg" "PICK3" == some (bin 1088 0, 1088, false)
#guard const "pce_cfg" "P64" == some (bin 32 7 ++ bin 32 9, 64, false)
#guard const "pce_cfg" "ONES" == some (bin 32 4, 32, false)
#guard const "pce_cfg" "DEC2" == some ("0100", 4, false)
#guard const "pce_cfg" "DEC3" == some ("1000", 4, false)
#guard const "pce_cfg" "XZF" == some ("1x0z01zx", 8, false)
#guard const "pce_cfg" "XZSEL" == some ("0z01", 4, false)
#guard const "pce_cfg" "XZCAT" == some ("01zx1x0z01zx", 12, false)
#guard const "pce_cfg" "SX65" ==
  some ("11111111111111111111111111111111111111111111111111111111111111110", 65, false)
#guard const "pce_cfg" "ZX65" ==
  some ("00000000000000000000000000000000011011110101011011011111011101111", 65, false)
#guard const "pce_cfg" "SUM33" == some ("111111111111111111111111111111011", 33, true)
#guard const "pce_cfg" "CARRY33" == some ("110111101010110110111110111011110", 33, false)
#guard const "pce_cfg" "PHI" == some (bin 32 7, 32, false)
#guard const "pce_cfg" "WFB" == some (bin 32 12, 32, false)

/-! The recursive function is not modelled: its constant is left unbound with
the reason, and this module, which does not read it, loads. -/
#guard const "pce_cfg" "F5" == none
#guard (match bindPackageEnums { int32 := true, functions := pceLeaf.pdesign.functions }
      pceLeaf.pdesign.enums with
    | .ok e => packageParamRefusals e pceLeaf.pdesign.packageParams
    | _ => []) ==
  ["package parameter 'pce_cfg::F5' is not bound: constant function 'pce_cfg::fact': function 'pce_cfg::fact': the call chain is longer than the number of functions (a recursive constant function is not modelled)"]

/-! The generate-local constant is computed per instance by a module function
called with the genvar (`PARAM ... GK0 2 GK1 3`): `q[g]` reads `a[GK]`. -/
private def genReads : List Nat :=
  match pceLeaf.e 4 with
  | .ok E => E.processes.toList.filterMap fun p =>
      match p with
      | .assign (.bitSel "q" _) (.bitSel (.ident "a") (.lit v)) => some v.toNat
      | _ => none
  | _ => []
#guard genReads == [2, 3]

/-! A module that reads the unbound constant in a process still loads (its
parameters, localparams and widths do not depend on it), and the read is a
loud node of the instantiated design, never a value. -/
load_design_sv2 pceRefused from
  "Examples/system-verilog/sem2/package_const_eval/pce_reads_refused.sv.json"
#guard (pceRefused.pdesign.instantiateD []).processes ==
  #[.assign "o" (.unsupported "ParamRef:package" "pce_cfg::F5")]

end Examples.«system-verilog».sem2.package_const_eval.agree
