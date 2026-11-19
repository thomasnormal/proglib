/- Canonical-E admission receipt for parser-native IEEE 1800-2023 inout ports. -/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.Inout
namespace Examples.«system-verilog».sem2.inout_wall.agree
open LeanModels.Sv LeanModels.Sv.Kernel
load_design_sv2 inoutWall from "Examples/system-verilog/sem2/inout_wall/inout_wall.sv.json"
#guard inoutWall.pdesign.decls.any (·.isInout)
#guard match inoutWall.pdesign.generates with
  | [.inst { conns := [.inout "pad" (some (.ident "pad")), _, _], .. }] => true
  | _ => false
#guard match inoutWall.pdesign.instantiate2 [] with
  | .unsupported msg => msg.contains "inout" && msg.contains "driver resolution"
  | _ => false

private def padNet : InoutNet :=
  { name := "pad", width := 1,
    drivers := [{ source := "child.pad", target := "pad" },
                { source := "external.pad", target := "pad" }] }

private def samplePad (child external : String) : String → Option LVec
  | "child.pad" => some (LVec.lit child)
  | "external.pad" => some (LVec.lit external)
  | _ => none

#guard (padNet.resolve (samplePad "z" "z")).toBinString == "z"
#guard (padNet.resolve (samplePad "1" "z")).toBinString == "1"
#guard (padNet.resolve (samplePad "z" "0")).toBinString == "0"
#guard (padNet.resolve (samplePad "1" "0")).toBinString == "x"
#guard InoutDrivesB padNet "child.pad" "pad"
end Examples.«system-verilog».sem2.inout_wall.agree
