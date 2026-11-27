import Lean
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

open LeanModels.Sv LeanModels.Sv.Kernel

def surveyOne (path : String) : IO String := do
  let text ← IO.FS.readFile path
  match parseEnvelope2String text with
  | .error e => return s!"PARSE|{e}"
  | .ok envl =>
      let pd := envl.design
      let args := pd.defaultArgs.toOption.getD []
      let admission :=
        if envl.lib.isEmpty then
          PDesign.instantiateE2 pd args (PDesign.surfaceFuel args)
        else
          PDesign.instantiateE2H pd envl.lib args
      match admission with
      | .timeout => return "REFUSED|Instantiation:E:timeout"
      | .unsupported message => return s!"REFUSED|{message}"
      | .ok design =>
          match design.initialState with
          | .timeout => return "INITIAL_TIMEOUT"
          | .unsupported message => return s!"INITIAL_REFUSED|{message}"
          | .ok state =>
              match design.step state [] with
              | .ok _ => return "ADMITTED|STEP_OK"
              | .timeout => return "ADMITTED|STEP_TIMEOUT"
              | .unsupported message => return s!"ADMITTED|STEP_REFUSED|{message}"

def main (args : List String) : IO UInt32 := do
  for path in args do
    let result ← surveyOne path
    IO.println s!"{path}|{result}"
  return 0
