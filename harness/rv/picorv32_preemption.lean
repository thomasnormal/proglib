import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.CoreMemResume

/-! Replay the two retained PicoRV32 ALU processes at a sampled clock edge.
All statement schedules start with the same process inputs. The surrounding core
supplies those inputs through the passive simulator probe. -/

open LeanModels.Sv LeanModels.Sv.Kernel

namespace PicoPreemption

private def checked {α} : Res α → IO α
  | .ok value => pure value
  | .unsupported message => throw (IO.userError message)
  | .timeout => throw (IO.userError "evaluation timed out")

private def uniqueWriter (all : List PProcess) (name : String) : Res PStmt := do
  match all.filter (fun p => (coreMemProcBlockingWrites p).contains name) with
  | [.alwaysImplicit body] => return body
  | _ => .unsupported s!"expected one retained @* writer of {name}"

structure Pair where
  e : CoreMemDesign
  bodies : Array PStmt
  sensitivity : Array (List ReadWin)
  writes : List String

def load (path : String) : IO Pair := do
  let .ok envelope := parseEnvelope2String (← IO.FS.readFile path)
    | throw (IO.userError "invalid retained envelope")
  let d := envelope.design
  let args ← checked d.defaultArgs
  let env ← checked (d.paramEnvH { int32 := true, functions := d.functions } args)
  let (raw, _) ← checked (coreMemExpandList env 4096 {} d.generates)
  let all := d.processes ++ coreMemDropGeneratedNetMarkers d raw
  let writer ← checked (uniqueWriter all "alu_add_sub")
  let reader ← checked (uniqueWriter all "alu_out_0")
  let bodies := #[writer, reader]
  let writes := (bodies.toList.flatMap coreMemStmtBlockingWrites).eraseDups
  let names := (writes ++ bodies.toList.flatMap coreMemStmtReadNames).eraseDups
  let selected := d.decls.filter fun dc => names.contains dc.name
  let decls ← checked (buildScalarDecls1 env selected)
  let elems ← checked (buildElems env selected)
  unless names.all (fun n => decls.any (fun dc => dc.name == n)) do
    throw (IO.userError "ALU projection has an unresolved signal")
  let env := { env with widths := decls.map fun dc => (dc.name, dc.width) }
  let e : CoreMemDesign := {
    name := d.name, env, elems, scalar := { decls := decls.toArray, procs := #[] },
    scalarEdge := { decls := decls.toArray, procs := #[] }, processes := #[], memories := #[] }
  return { e, bodies, writes, sensitivity := bodies.map fun b => (instStmt2 env elems b).rawReads }

structure Slot where
  store : CoreMemState
  view : SvState
  active : Array (Option CombCursor)

/-- A process leaves its event control on the first change to a sensed window.
Its pending continuation consumes all later changes until it reaches the wait. -/
private def wake (pair : Pair) (before after : SvState)
    (active : Array (Option CombCursor)) : Array (Option CombCursor) :=
  active.mapIdx fun i cursor =>
    if cursor.isNone && pair.sensitivity[i]!.any (fun r => !decide (r.agree before after))
    then some (CombCursor.start pair.e.env pair.bodies[i]!)
    else cursor

private def step (pair : Pair) (slot : Slot) (i : Nat) : IO Slot := do
  let some cursor := slot.active[i]?.join | throw (IO.userError s!"process {i} is waiting")
  let (store, view, next) ← checked (cursor.resume pair.e slot.store slot.view)
  let active := wake pair slot.view view slot.active
  return { store, view, active := active.set! i (if next.work.isEmpty then none else some next) }

deriving instance BEq for IEnv
deriving instance BEq for CombWork
deriving instance BEq for CombCursor

/-- This projection contains only scalar declarations. Compare both the typed
store image and the threaded view, along with all pending work and locals. -/
private def sameState (pair : Pair) (a b : Slot) : Bool :=
  a.view == b.view && a.active == b.active &&
    pair.e.scalar.view a.store.scalar == pair.e.scalar.view b.store.scalar

/-- Expand every ready choice at each depth. A budget hit fails the check.
Only equal configurations in the same frontier are coalesced. -/
private def explore (pair : Pair) (start : Slot) : IO (Array (String × String) × Nat) := do
  let mut frontier := #[start]
  let mut outcomes := #[]
  let mut visited := 0
  for _ in [:180] do
    let mut next := #[]
    for s in frontier do
      visited := visited + 1
      if s.active.all Option.isNone then
        unless s.view.showSignal "alu_eq" == "1" do throw (IO.userError "ALU equality did not settle")
        let row := (s.view.showSignal "alu_out_0", s.view.showSignal "alu_out")
        unless outcomes.contains row do outcomes := outcomes.push row
      for i in [:s.active.size] do
        if s.active[i]!.isSome then
          let successor ← step pair s i
          unless next.any (sameState pair successor) do next := next.push successor
    if next.isEmpty then return (outcomes, visited)
    frontier := next
  throw (IO.userError "ALU schedule exploration exceeded its depth bound")

private def runSerial (pair : Pair) (start : Slot) : IO Slot := do
  let mut s := start
  for _ in [:180] do
    let some i := s.active.findIdx? Option.isSome | return s
    s ← step pair s i
  throw (IO.userError "serial ALU execution exceeded its depth bound")

def replay (pair : Pair) (path cycle expectedOther : String) : IO Unit := do
  let mut pre : SvState := []
  let mut post : SvState := []
  for line in ← IO.FS.lines path do
    let ["SNAP", t, phase, name, digits] := line.splitOn " " | continue
    if t != cycle then continue
    let some v := LVec.ofString? digits | throw (IO.userError s!"invalid sample {line}")
    unless pair.e.scalarWidth? name == some v.width do throw (IO.userError s!"bad width for {name}")
    match phase with
    | "0" => pre := (name, v) :: pre
    | "1" => post := (name, v) :: post
    | _ => throw (IO.userError s!"bad phase {phase}")
  for data in [pre, post] do
    let names := data.map Prod.fst
    unless names.length == pair.e.scalar.decls.size && names.eraseDups.length == names.length do
      throw (IO.userError s!"incomplete or duplicate cycle {cycle} samples")
  let old := pre.foldl (fun s (n, v) => pair.e.setScalarState s n v) pair.e.initial
  let initial := post.foldl (fun s (n, v) =>
      if pair.writes.contains n then s else pair.e.setScalarState s n v) old
  let view := pair.e.scalar.view initial.scalar
  let start : Slot := ⟨initial, view, wake pair pre view #[none, none]⟩
  let serial ← runSerial pair start
  unless pair.writes.all (fun n => serial.view.lookup n == post.lookup n) do
    throw (IO.userError "uninterrupted execution differs from the observed ALU outputs")
  let (outcomes, visited) ← explore pair start
  let expected := ["1", expectedOther].map fun bit => (bit, ((LVec.lit bit).resizeU 32).toBinString)
  unless outcomes.size == expected.length && expected.all outcomes.contains do
    throw (IO.userError s!"unexpected settled outputs at cycle {cycle}: {outcomes}")
  IO.println s!"cycle {cycle}: exhausted {visited} configurations across depths, settled outputs {outcomes}"

end PicoPreemption

def main (args : List String) : IO Unit := do
  match args with
  | ["signals", path] =>
      for decl in (← PicoPreemption.load path).e.scalar.decls do IO.println decl.name
  | ["replay", path, known, program] =>
      let pair ← PicoPreemption.load path
      PicoPreemption.replay pair known "12" "0"
      PicoPreemption.replay pair program "28" "x"
  | _ => throw (IO.userError "expected signals ENVELOPE or replay ENVELOPE KNOWN PROGRAM")
