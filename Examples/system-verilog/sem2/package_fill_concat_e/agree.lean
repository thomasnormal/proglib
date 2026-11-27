/- A parser-native constant-expression receipt for unbased unsized fills in
   concatenations.  IEEE 1800-2023 §5.7.1 gives each fill operand its one-bit
   self-determined width in a concatenation, while §10.8 applies the enclosing
   packed target width. -/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec
namespace Examples.«system-verilog».sem2.package_fill_concat_e.agree
open LeanModels.Sv LeanModels.Sv.Kernel

load_design_sv2 fillConcat from
  "Examples/system-verilog/sem2/package_fill_concat_e/package_fill_concat_e.sv.json"

#guard fillConcat.pdesign.crossCheckFull == ([], 9)
#guard fillConcat.pdesign.localParams.map (fun l => (l.name, l.resolved?)) ==
  [("K0", some 1), ("K1", some 2), ("U0", some 1), ("U1", some 3)]

def outputs (w : Nat) : Res (List (String × String × String × String)) := do
  let E ← fillConcat.e w
  let rows ← runCoreMemRows E E.initial [[]]
  .ok (rows.map fun s =>
    (SvState.showSignal (CoreMemState.view E s) "k0",
     SvState.showSignal (CoreMemState.view E s) "k1",
     SvState.showSignal (CoreMemState.view E s) "u0",
     SvState.showSignal (CoreMemState.view E s) "u1"))

#guard outputs 4 == .ok [("00001", "00010", "01", "11")]
#guard outputs 8 == .ok [("000000001", "000000010", "01", "11")]

end Examples.«system-verilog».sem2.package_fill_concat_e.agree
