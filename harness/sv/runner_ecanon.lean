/- Canonical-E differential backend.  It executes `CoreMemDesign.step`, the
source-shaped canonical E slot with native memory and the same refusal path as
the elaborator. -/

import Lean
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

open Lean (Json)
open LeanModels.Sv
open LeanModels.Sv.Kernel

namespace SvCanonicalEHarness

def getF (j : Json) (name : String) : Except String Json :=
  match j.getObjVal? name with
  | .ok v => .ok v
  | .error _ => .error s!"missing field '{name}'"

def getOpt (j : Json) (name : String) : Option Json :=
  match j.getObjVal? name with
  | .ok .null => none
  | .ok v => some v
  | .error _ => none

def getStr (j : Json) (name : String) : Except String String := do
  match (← getF j name).getStr? with
  | .ok s => .ok s
  | .error _ => .error s!"field '{name}' is not a string"

def getArr (j : Json) (name : String) : Except String (Array Json) := do
  match (← getF j name).getArr? with
  | .ok a => .ok a
  | .error _ => .error s!"field '{name}' is not an array"

def findCase (cases : Array Json) (name : String) : Except String Json := do
  for c in cases do
    if (← getStr c "name") == name then return c
  .error s!"case '{name}' not found"

def resolvePoint (pd : PDesign) (paramsJ : Option Json) : Except String (PDesign × List Int) :=
  pd.atPoint <| pd.params.map fun p =>
    match paramsJ with
    | some j => (j.getObjVal? p.name).toOption.bind (·.getInt?.toOption)
    | none => none

def parseEntry (decls : List Decl) (j : Json) : Except String SvState := do
  match j with
  | .obj kvs =>
      let mut st : SvState := []
      for (name, v) in kvs.toArray do
        let bits ← match v.getStr? with
          | .ok s => pure s
          | .error _ => .error s!"stimulus '{name}' is not a string"
        let some lv := LVec.ofString? bits
          | .error s!"stimulus '{name}': bad digits {bits}"
        let some dc := decls.find? (·.name == name)
          | .error s!"stimulus '{name}': not a declared signal"
        unless dc.isInput do .error s!"stimulus '{name}': not an input port"
        unless lv.width == dc.width do
          .error s!"stimulus '{name}': width {lv.width} ≠ port width {dc.width}"
        st := st ++ [(name, lv)]
      return st
  | _ => .error "stimulus entry is not an object"

def lowAfterSample (E : CoreMemDesign) (clock edge : String) (st : CoreMemState) : CoreMemState :=
  let value := if edge == "negedge" then LVec.ofNat 1 1 else LVec.ofNat 1 0
  E.compactScalar st (SvState.set (E.scalar.view st.scalar) clock value)

def addClock (clock : String) (edge : String) : List SvState → List SvState
  | [] => []
  | row :: rest =>
      let value := if edge == "negedge" then LVec.ofNat 1 0 else LVec.ofNat 1 1
      SvState.set row clock value :: addClock clock edge rest

end SvCanonicalEHarness

open SvCanonicalEHarness in
def main (argv : List String) : IO UInt32 := do
  let err (msg : String) : IO UInt32 := do
    (← IO.getStderr).putStrLn s!"ERROR: {msg}"
    return 1
  let argv := match argv with | [e, c, n, s, _p] => [e, c, n, s] | xs => xs
  match argv with
  | [envPath, casesPath, caseName, _sigma] => do
      let envText ← IO.FS.readFile ⟨envPath⟩
      let casesText ← IO.FS.readFile ⟨casesPath⟩
      let r : Except String (CoreMemDesign × List SvState × List String × Nat × String × String) := do
        let (pd, lib) ← loadHierString envText
        let cj ← Json.parse casesText
        let case ← findCase (← getArr cj "cases") caseName
        let (pd, args) ← resolvePoint pd (getOpt case "params")
        let d ← match if lib.isEmpty then PDesign.instantiateE2 pd args
            else PDesign.instantiateE2H pd lib args with
          | .ok d => pure d
          | .timeout => .error "instantiateE2: timeout"
          | .unsupported m => .error s!"instantiateE2: {m}"
        let stim0 ← (← getArr case "stimulus").toList.mapM (parseEntry d.scalar.decls.toList)
        let signals ← (← getArr case "signals").toList.mapM (·.getStr?)
        let fuel := (getOpt cj "fuel").bind (·.getNat?.toOption) |>.getD 4096
        let clock := (getOpt case "clock").bind (·.getStr?.toOption) |>.getD "clk"
        let edge := (getOpt case "clock_edge").bind (·.getStr?.toOption) |>.getD "posedge"
        pure (d, addClock clock edge stim0, signals, fuel, clock, edge)
      match r with
      | .error e => err e
      | .ok (d, stim, signals, fuel, clock, edge) =>
          let out ← IO.getStdout
          for dc in d.scalar.decls.toList do
            let sign := if dc.isSigned then "signed" else "unsigned"
            if dc.isInput then out.putStrLn s!"PORT {dc.name} in {dc.width} {sign}"
            else if dc.isOutput then out.putStrLn s!"PORT {dc.name} out {dc.width} {sign}"
          match d.initialState with
          | .timeout => err "canonical E initial: timeout"
          | .unsupported m => err s!"canonical E initial: unsupported: {m}"
          | .ok initial =>
              let rec loop (k : Nat) (st : CoreMemState) : List SvState → IO UInt32
                | [] => pure 0
                | row :: rest =>
                    match d.step st row with
                    | .timeout => err "canonical E step: timeout"
                    | .unsupported m => err s!"canonical E step: unsupported: {m}"
                    | .ok next => do
                        let sampled := lowAfterSample d clock edge next
                        let cells := signals.map fun s => s!"{s}={SvState.showSignal (d.scalar.view sampled.scalar) s}"
                        out.putStrLn (s!"CYCLE {k} " ++ " ".intercalate cells)
                        loop (k + 1) sampled rest
              loop 0 initial stim
  | _ => err "usage: runner_ecanon.lean <envelope.sv.json> <cases2.json> <case> <src|rev> [<probes.json>]"
