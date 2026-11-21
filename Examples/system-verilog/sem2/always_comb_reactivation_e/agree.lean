/-
Canonical-E receipt for IEEE 1800-2023 §9.2.2.2.1.  An always_comb
process is not reactivated by a variable written by that same process.
The source-shaped self-read fixtures stay outside the static equation gate,
but the canonical executor must still retain the simulator-visible previous
value instead of iterating to a fixed point.
-/
import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemExec

namespace Examples.«system-verilog».sem2.always_comb_reactivation_e

open LeanModels.Sv LeanModels.Sv.Kernel

def asIO {α : Type} : Res α → IO α
  | .ok x => pure x
  | .timeout => throw (IO.userError "canonical E timeout")
  | .unsupported msg => throw (IO.userError msg)

def trace (path : String) (rows : List SvState) (signals : List String) : IO (List String) := do
  let text ← IO.FS.readFile path
  let pd ← match loadPDesignString text with
    | .ok x => pure x
    | .error msg => throw (IO.userError msg)
  let d ← asIO (PDesign.instantiateE2 pd [])
  let initial ← asIO d.initialState
  let states ← asIO (runCoreMemRows d initial rows)
  pure (states.map fun st =>
    let view := CoreMemState.view d st
    String.intercalate " " (signals.map view.showSignal))

def combRows : List SvState :=
  ["00", "01", "01", "10", "1x", "00"].map fun a => [("a", LVec.lit a)]

def heldRows : List SvState :=
  [("0", "00", "00"), ("1", "01", "00"), ("0", "01", "01"),
   ("1", "00", "01"), ("x", "01", "00"), ("1", "01", "00"),
   ("0", "00", "01"), ("z", "01", "01")].map
    fun (c, a, b) => [("c", LVec.lit c), ("a", LVec.lit a), ("b", LVec.lit b)]

def selfRows : List SvState :=
  ["1", "0", "1", "1", "x", "0", "1"].map fun a => [("a", LVec.lit a)]

def check : IO Unit := do
  let comb ← trace "Examples/system-verilog/sem2/rbw_comb/rbw_comb.sv.json" combRows ["y", "t"]
  let held ← trace "Examples/system-verilog/sem2/rbw_held/rbw_held.sv.json" heldRows ["y", "t"]
  let self ← trace "Examples/system-verilog/sem2/rbw_selfinc/rbw_selfinc.sv.json" selfRows ["y"]
  unless comb == ["xx 00", "00 01", "00 01", "01 10", "10 1x", "1x 00"] do
    throw (IO.userError s!"rbw_comb E trace: {comb}")
  unless held == ["xx 00", "01 00", "00 01", "00 01", "01 00", "01 00", "00 01", "01 01"] do
    throw (IO.userError s!"rbw_held E trace: {held}")
  unless self == ["x1", "10", "01", "01", "1x", "x0", "01"] do
    throw (IO.userError s!"rbw_selfinc E trace: {self}")
  IO.println "canonical E: 21 always_comb self-write rows MATCH"

#eval check

end Examples.«system-verilog».sem2.always_comb_reactivation_e
