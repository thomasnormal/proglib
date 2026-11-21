import LeanModels.Sv.Kernel.Core1Elab
import LeanModels.Sv.Kernel.AggregateBridge
import LeanModels.Sv.Kernel.MemElab
import LeanModels.Sv.Loop2
import LeanModels.Sv.Plusargs

/-!
# Source-shaped one-rank memories in canonical E

This is the first memory extension of E-core-1.  The scalar part is the
canonical `Store`/`Elab1` store and its scalar NBA queue; unpacked storage is
one native `MemState`.  The source `PStmt` is retained, including a procedural
`forLoop`, and the loop is evaluated from `Loop2.headerSchema` at run time.

The adapter is deliberately small: one-rank unpacked declarations, retained edge clocks (including negative
edges), continuous scalar assignments, one-shot time-zero initialization,
and a retained plain `always @*` body with raw-read sensitivity.  It does not
lower a loop to a block, expand a memory into cells, or introduce another
memory representation.  Unknown and out-of-range memory indices use
`MemState.issueNba`/`readIndexId`, so issue-time NBA sampling and x/no-op
behavior are shared with the canonical memory component.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

/-! ## Source-shaped elaboration -/

structure CoreMemDecl where
  source : PDecl
  shape : MemShape
deriving Repr, Inhabited

structure CoreMemAggDecl where
  source : PDecl
  ty : AggType
  id : VarId
deriving Repr, Inhabited

structure CoreMemEdge where
  clock : String
  edge : ClockEdge := .posedge
  reset : Option String := none
  /-- Polarity of the asynchronous reset event (§9.4.2).  `false` is the
      active-low form (`negedge`); `true` is the active-high form
      (`posedge`). -/
  resetHigh : Bool := false
  body : PStmt
  style : EdgeStyle := .alwaysFF
deriving Repr, Inhabited

structure CoreMemEvent where
  signal : String
  edge : PEventEdge := .any
deriving Repr, Inhabited

inductive CoreMemProc where
  | edge (p : CoreMemEdge)
  | assign (target : PLhs) (value : PExpr)
  | primitive (op : String) (target : PLhs) (inputs : List PExpr)
  | initial (body : PStmt)
  /-- An `always_comb` body runs once at time zero and is reactivated when a
      value in its implicit sensitivity set changes.  The retained `PStmt`
      stays source-shaped; this route does not lower it to `Process2`. -/
  | comb (body : PStmt)
  /-- A plain `always @*` waits for a raw read change before activation.
      Its source body remains a `PStmt`; the memory route does not lower it
      into a clocked or combinational surrogate. -/
  | implicit (body : PStmt)
  /-- Plain `always` event list, retained source-shaped until publication. -/
  | event (events : List CoreMemEvent) (body : PStmt)
  /-- A level-sensitive `always_latch`; its source node uses the exact
      implicit-sensitivity executor while remaining distinct in the AST. -/
  | latch (body : PStmt)
  | unsupported (kind text : String)
deriving Repr, Inhabited

structure CoreMemDesign where
  name : String
  env : IEnv
  /-- Command-line plus-arguments supplied to system functions such as
      `$test$plusargs` (§20.2.2).  The host must provide this explicitly. -/
  plusargs : List String := []
  /-- Element widths for the retained source declarations.  `instExpr2`
      needs this table to lower a packed bit select; keeping it beside the
      source-shaped design avoids manufacturing a second declaration view. -/
  elems : List (String × Nat)
  scalar : Elab
  scalarEdge : Elab1
  memories : Array CoreMemDecl
  aggregates : Array CoreMemAggDecl := #[]
  processes : Array CoreMemProc
  /-- Parser-retained literal `$readmemh` metadata; no host file is read. -/
  readmemh : List PReadmemh := []
  /--
  Instantiated scalar continuous-assignment expressions, aligned with
  `processes`.  These are a derived cache only: the source `PExpr` remains in
  every `CoreMemProc`, and expressions which read native memory continue
  through `evalExpr` below.  Keeping this cache on the design avoids running
  the parameter-width elaborator once per time-zero settle pass.
  -/
  compiledAssigns : Array (Option Expr2) := #[]
  /--
  Instantiated pure raw-sensitivity expressions, aligned with `processes`.
  Memory and function-call reads stay absent so their source-shaped evaluator
  remains the authority for stateful reads.
  -/
  compiledCombReads : Array (Option (List Expr2)) := #[]
  /-- Pure raw-read expressions for retained plain `always @*` bodies. -/
  compiledImplicitReads : Array (Option (List Expr2)) := #[]
  /-- Module nets with several full-width equal-strength continuous drivers.
      The source-shaped assignment nodes stay in `processes`; this list only
      records where the §6.6 resolver is applied while those nodes settle. -/
  resolvedNets : List String := []
  /-- Source-shaped declaration initializers whose value depends on the
      initial state.  They execute in declaration order before retained
      `initial` processes (§6.8), without lowering the declaration node. -/
  declInitializers : List (String × PExpr × Nat) := []
deriving Inhabited

/-- Install the simulator's explicit plus-argument environment on a design.
    This keeps `$test$plusargs` dependent on an input chosen by the caller,
    rather than on an ambient process or a fixed simulator result. -/
def CoreMemDesign.withPlusargs (E : CoreMemDesign) (plusargs : List String) : CoreMemDesign :=
  { E with plusargs }

/-! A structural admission predicate for the canonical memory family.  This is
not a scalar `Design2` coercion: memory declarations remain source-shaped
`MemShape`s, and the process check is deliberately only an admission check.
Equation tactics must add their own memory-aware obligations before claiming a
settled result. -/
def coreMemSupportedB : List CoreMemProc → Bool
  | [] => true
  | .unsupported _ _ :: _ => false
  | _ :: rest => coreMemSupportedB rest

def coreMemNamesUniqueB : List String → Bool
  | [] => true
  | n :: rest => (!rest.contains n) && coreMemNamesUniqueB rest

def CoreMemDesign.Structure (d : CoreMemDesign) : Prop :=
  coreMemNamesUniqueB (d.memories.toList.map (fun m => m.source.name)) = true ∧
    coreMemSupportedB d.processes.toList = true

/-! The first equation gate is intentionally conservative: it admits only the
source-shaped continuous assignments whose scalar or one-rank memory target is
already represented by `CoreMemDesign.settleAssign`.  Clocked and procedural
equations remain loud until their memory-aware equation theorem is added. -/
def coreMemEquationB : List CoreMemProc → Bool
  | [] => true
  | .assign (.ident _) _ :: rest => coreMemEquationB rest
  | .assign (.bitSel _ _) _ :: rest => coreMemEquationB rest
  | .assign (.partSel _ _ _) _ :: rest => coreMemEquationB rest
  | .assign (.arrayPart _ [] .range _ _) _ :: rest => coreMemEquationB rest
  | .assign (.arrayPart _ [] .up _ _) _ :: rest => coreMemEquationB rest
  | .assign (.arrayPart _ [] .down _ _) _ :: rest => coreMemEquationB rest
  | .assign (.arrayElem _ []) (.arrayElem _ []) :: rest => coreMemEquationB rest
  | .assign (.arrayElem _ [_]) _ :: rest => coreMemEquationB rest
  | _ => false

def CoreMemDesign.EquationGate (d : CoreMemDesign) : Prop :=
  CoreMemDesign.Structure d ∧ coreMemEquationB d.processes.toList = true

instance : DecidablePred CoreMemDesign.Structure := fun d => by
  unfold CoreMemDesign.Structure
  infer_instance

instance : DecidablePred CoreMemDesign.EquationGate := fun d => by
  unfold CoreMemDesign.EquationGate
  infer_instance

structure CoreMemState where
  scalar : Store
  /-- Data-backed scalar values, indexed by the flat declaration ordinal.
      The canonical `Store` view is rebuilt from this array after each
      source-shaped update, so sequential assignments do not form a chain of
      `Store.set` closures. -/
  scalarCache : Array Val
  memory : MemState
  aggregates : AggStore

/-! The scalar E store is a function for compatibility with canonical E.  The
    cache is the state representation; this direct view avoids rebuilding a
    `Store.set` closure chain when a source-shaped hierarchy assigns several
    scalar outputs during one settle pass. -/
def CoreMemDesign.scalarStore (E : CoreMemDesign) (cache : Array Val) : Store :=
  fun x =>
    match x.path with
    | [] =>
        match cache[x.decl]? with
        | some v => v
        | none => E.scalar.initStore x
    | _ => E.scalar.initStore x

def CoreMemDesign.scalarCacheOf (E : CoreMemDesign) (s : Store) : Array Val :=
  Array.ofFn (n := E.scalar.decls.size) fun i => s { decl := i.val }

def CoreMemDesign.setScalarState (E : CoreMemDesign) (st : CoreMemState)
    (name : String) (v : LVec) : CoreMemState :=
  match E.scalar.resolve name with
  | some x =>
      let cache := st.scalarCache.set! x.decl (Val.ofLVec (st.scalar x).ty v)
      { st with scalar := E.scalarStore cache, scalarCache := cache }
  | none => st

def CoreMemDesign.normalizeScalar (E : CoreMemDesign) (st : CoreMemState)
    (s : Store) : CoreMemState :=
  let cache := E.scalarCacheOf s
  { st with scalar := E.scalarStore cache, scalarCache := cache }

/-! A threaded view is the authoritative name-facing image while one source
body settles.  Materializing it back into a flat `Store` at process
boundaries preserves the E store meaning but avoids an ever-growing chain of
`Store.set` closures after many scalar assignments. -/
def CoreMemDesign.storeFromView (E : CoreMemDesign) (view : SvState) : Store :=
  fun x =>
    match E.scalar.declOf x with
    | some dc =>
        let fallback := if dc.isNet then LVec.replicate dc.width .lz else LVec.xVec dc.width
        Val.ofLVec (VType.ofDecl dc) ((SvState.lookup view dc.name).getD fallback)
    | none => default

def CoreMemDesign.compactScalar (E : CoreMemDesign) (st : CoreMemState) (view : SvState) :
    CoreMemState :=
  if E.scalar.view st.scalar = view then
    st
  else
    let cache := E.scalarCacheOf (E.storeFromView view)
    { st with scalar := E.scalarStore cache, scalarCache := cache }

def CoreMemDesign.resetResolvedNets (E : CoreMemDesign) (st : CoreMemState) : CoreMemState :=
  E.resolvedNets.foldl (fun acc name =>
    match E.scalar.resolve name with
    | some x =>
        match E.scalar.declOf x with
        | some dc => E.setScalarState acc name (LVec.replicate dc.width .lz)
        | none => acc
    | none => acc) st

theorem CoreMemDesign.compactScalar_of_view_eq
    (E : CoreMemDesign) (st : CoreMemState) (view : SvState)
    (h : E.scalar.view st.scalar = view) :
    E.compactScalar st view = st := by
  simp [CoreMemDesign.compactScalar, h]

def CoreMemDesign.initial (E : CoreMemDesign) : CoreMemState :=
  let cache := E.scalarCacheOf E.scalar.initStore
  { scalar := E.scalarStore cache
    scalarCache := cache
    memory := MemState.ofShapes (E.memories.toList.map CoreMemDecl.shape)
    aggregates := AggStore.ofCells (E.aggregates.toList.map fun d =>
      (d.id, { ty := d.ty, value := .unknown d.ty })) }

def CoreMemDesign.scalarAssignInputsOnly (E : CoreMemDesign) : Bool :=
  E.memories.isEmpty && E.processes.toList.all fun p =>
    match p with
    | .assign (.ident _) (.ident n) =>
        match E.scalar.resolve n with
        | some x => (E.scalar.declOf x).map (·.isInput) |>.getD false
        | none => false
    | _ => false

def CoreMemDesign.memDecl? (E : CoreMemDesign) (name : String) : Option CoreMemDecl :=
  E.memories.toList.find? (fun d => d.source.name == name)

def CoreMemDesign.aggregateDecl? (E : CoreMemDesign) (name : String) : Option CoreMemAggDecl :=
  E.aggregates.toList.find? (fun d => d.source.name == name)

def CoreMemDesign.scalarWidth? (E : CoreMemDesign) (name : String) : Option Nat :=
  match E.scalar.resolve name with
  | some x => (E.scalar.declOf x).map Decl.width
  | none => none

def CoreMemDesign.scalarE (E : CoreMemDesign) : Elab1 := E.scalarEdge

def CoreMemDesign.hasImplicit (E : CoreMemDesign) : Bool :=
  E.processes.toList.any fun p =>
    match p with
    | .implicit _ => true
    | _ => false

def CoreMemDesign.hasComb (E : CoreMemDesign) : Bool :=
  E.processes.toList.any fun p =>
    match p with
    | .comb _ | .latch _ => true
    | _ => false

def CoreMemDesign.compileAssigns (E : CoreMemDesign) : Array (Option Expr2) :=
  E.processes.map fun p =>
    match p with
    | .assign (.ident name) value =>
        match E.scalarWidth? name with
        | some width => some (instExpr2 E.env E.elems (some width) value)
        | none => none
    | _ => none

def instScalarDecl1 (env : IEnv) (pd : PDecl) : Res (Option Decl) :=
  if pd.aggregate?.isSome || !pd.unpackedDims.isEmpty then
    .ok none
  else
    match pd.type.width env with
    | .error e => .unsupported s!"decl '{pd.name}': {e}"
    | .ok w =>
        match pd.init with
        | none =>
            let dc : Decl :=
              { name := pd.name, width := w, isSigned := pd.isSigned,
                isNet := pd.isNet, twoState := pd.twoState,
                isInput := pd.isInput, isOutput := pd.isOutput,
                -- IEEE 1800-2023 §6.6: an undriven four-state net reads z
                -- at time zero.  This also covers output-wire ports admitted
                -- as a single generated driver; the retained declaration is
                -- still a net and must not inherit the variable x start.
                init := if pd.isNet then some (LVec.replicate w .lz) else none }
            .ok (some dc)
        | some init =>
            match instExpr env (some w) init with
            | .lit v =>
                let dc : Decl :=
                  { name := pd.name, width := w, isSigned := pd.isSigned,
                    isNet := pd.isNet, twoState := pd.twoState,
                    isInput := pd.isInput, isOutput := pd.isOutput, init := some v }
                .ok (some dc)
            | _ =>
                -- Match the scalar declaration route: an INT-class constant
                -- such as `logic [1:0] value = -1` is context-sized at the
                -- declaration width (§6.8, §11.8).  Signal-dependent
                -- initializers remain a loud refusal.
                match evalInt env init with
                | .ok v =>
                    let dc : Decl :=
                      { name := pd.name, width := w, isSigned := pd.isSigned,
                        isNet := pd.isNet, twoState := pd.twoState,
                        isInput := pd.isInput, isOutput := pd.isOutput,
                        init := some (LVec.ofInt w v) }
                    .ok (some dc)
                | .error _ =>
                    let dc : Decl :=
                      { name := pd.name, width := w, isSigned := pd.isSigned,
                        isNet := pd.isNet, twoState := pd.twoState,
                        isInput := pd.isInput, isOutput := pd.isOutput, init := none }
                    .ok (some dc)

def buildScalarDecls1 (env : IEnv) : List PDecl → Res (List Decl)
  | [] => .ok []
  | pd :: rest => do
      let dc? ← instScalarDecl1 env pd
      let rest' ← buildScalarDecls1
        (match dc? with
         | some dc => { env with widths := (pd.name, dc.width) :: env.widths }
         | none => env) rest
      match dc? with
      | some dc => .ok (dc :: rest')
      | none => .ok rest'

def coreMemDeclInitializers (env : IEnv) : List PDecl → Res (List (String × PExpr × Nat))
  | [] => .ok []
  | pd :: rest => do
      let tail ← coreMemDeclInitializers env rest
      match pd.init, pd.type.width env with
      | some init, .ok width =>
          match instExpr env (some width) init with
          | .lit _ => .ok tail
          | _ => .ok ((pd.name, init, width) :: tail)
      | _, _ => .ok tail

def buildMemDecls1 (env : IEnv) : List PDecl → Nat → Res (List CoreMemDecl)
  | [], _ => .ok []
  | pd :: rest, ordinal => do
      let tail ← buildMemDecls1 env rest (ordinal + 1)
      match pd.memShapeWithId? env ({ decl := ordinal } : MemId) with
      | .error e => .unsupported e
      | .ok none => .ok tail
      | .ok (some shape) => .ok ({ source := pd, shape } :: tail)

def buildAggDecls1 (env : IEnv) : List PDecl → Nat → Res (List CoreMemAggDecl)
  | [], _ => .ok []
  | pd :: rest, ordinal => do
      let tail ← buildAggDecls1 env rest (ordinal + 1)
      match pd.aggregate? with
      | none => .ok tail
      | some _ => do
          let ty ← match LeanModels.Sv.Kernel.PDecl.aggregateType? env pd with
            | .ok ty => .ok ty
            | .error msg => .unsupported msg
          .ok ({ source := pd, ty, id := { decl := ordinal } } :: tail)

def CoreMemProc.ofPProcess : PProcess → CoreMemProc
  | .alwaysFF clock body => .edge { clock, body, style := .alwaysFF }
  | .alwaysFFNegedge clock body => .edge { clock, edge := .negedge, body, style := .alwaysFF }
  | .alwaysPlain clock body => .edge { clock, body, style := .alwaysPlain }
  | .alwaysFFR clock reset body high =>
      .edge { clock, reset := some reset, resetHigh := high, body, style := .alwaysFF }
  | .assign target value => .assign (.ident target) value
  | .assignL target value => .assign target value
  | .alwaysComb body => .comb body
  | .alwaysLatch body => .latch body
  | .alwaysImplicit body => .implicit body
  | .alwaysEvent events body => .event (events.map fun e => { signal := e.signal, edge := e.edge }) body
  | .initial body => .initial body
  | .unsupported kind text => .unsupported kind text

/-! Initial elaboration checks are source-shaped `initial` parser nodes, but
their only observable effect is the diagnostic on a failed parameter point.
Reuse Param2's exact constant-check admission in canonical E and turn a
passing check into the same inert empty process used by the scalar E view.
Runtime initial bodies are retained for the explicit time-zero executor;
unsupported statements still refuse from `initialState` with their own clause
message rather than being executed as ordinary cycle-time statements. -/
def CoreMemProc.ofPProcessAt (env : IEnv) : PProcess → CoreMemProc
  | .initial body =>
      match initialCheckAdmits env body with
      | .ok () => .comb (.block [])
      | .error _ => .initial body
  | p => CoreMemProc.ofPProcess p

def CoreMemProc.ofPPrimitive (p : PPrimitive) : CoreMemProc :=
  .primitive p.op p.target p.inputs

def coreMemEventEdge : PEventEdge → ClockEdge → Bool
  | .any, _ => true
  | .posedge, _ => true
  | .negedge, _ => true

def coreMemEventFires (old new : SvState) (e : CoreMemEvent) : Bool :=
  match e.edge with
  | .any => SvState.bit0 old e.signal != SvState.bit0 new e.signal
  | .posedge => isPosedge (SvState.bit0 old e.signal) (SvState.bit0 new e.signal)
  | .negedge => isNegedge (SvState.bit0 old e.signal) (SvState.bit0 new e.signal)

def coreMemEventsFire (old new : SvState) : List CoreMemEvent → Bool
  | [] => false
  | e :: rest => coreMemEventFires old new e || coreMemEventsFire old new rest

/-! Canonical E's one-slot transition compares the slot's starting view with
the settled pre-edge view.  IEEE 1800-2023 §§4.4 and 9.4.2 instead schedule a
new active pass when an NBA changes a clock or asynchronous reset.  Until the
event-queue transport is modelled, refuse those source-shaped events unless
their signal is a top-level input port. -/

def coreMemInputPortB (d : PDesign) (name : String) : Bool :=
  d.decls.any (fun pd => pd.name == name && pd.isInput)

/-! A single source-shaped process activation may issue several updates to the
same signal.  In the NBA region each assignment is a distinct update event
(IEEE 1800-2023 §4.6), and blocking assignments expose each intermediate
value immediately (§10.4.1).  The canonical E pass currently commits an
activation as one retained state transition, so it cannot preserve an edge
that occurs between two writes.  Refuse the syntactic sufficient shape: an
edge source (clock or asynchronous-reset signal) is written at least twice
in any one retained process body.  This is deliberately conservative across
branches; proving that two writes are mutually exclusive belongs to the
event-queue scheduler, not this admission check.
-/

mutual

def coreMemStmtWrites : PStmt → List String
  | .localDecl name _ _ => [name]
  | .automaticDecl _ _ _ => []
  | .blockingAssign name _ | .nbaAssign name _ => [name]
  | .ifStmt _ yes none => coreMemStmtWrites yes
  | .ifStmt _ yes (some no) => coreMemStmtWrites yes ++ coreMemStmtWrites no
  | .block body => coreMemStmtWritesList body
  | .forLoop _ _ _ _ body => coreMemStmtWrites body
  | .blockingAssignL target _ | .nbaAssignL target _ => [target.name]
  | .caseStmt _ items none _ _ => coreMemCaseWrites items
  | .caseStmt _ items (some defaultBody) _ _ =>
      coreMemCaseWrites items ++ coreMemStmtWrites defaultBody
  | .unsupported _ _ => []

def coreMemStmtWritesList : List PStmt → List String
  | [] => []
  | stmt :: rest => coreMemStmtWrites stmt ++ coreMemStmtWritesList rest

def coreMemCaseWrites : List (List PExpr × PStmt) → List String
  | [] => []
  | item :: rest => coreMemStmtWrites item.2 ++ coreMemCaseWrites rest

def coreMemStmtBlockingWrites : PStmt → List String
  | .localDecl name _ _ => [name]
  | .automaticDecl _ _ _ => []
  | .blockingAssign name _ => [name]
  | .nbaAssign _ _ => []
  | .ifStmt _ yes none => coreMemStmtBlockingWrites yes
  | .ifStmt _ yes (some no) =>
      coreMemStmtBlockingWrites yes ++ coreMemStmtBlockingWrites no
  | .block body => coreMemStmtBlockingWritesList body
  | .forLoop _ _ _ _ body => coreMemStmtBlockingWrites body
  | .blockingAssignL target _ => [target.name]
  | .nbaAssignL _ _ => []
  | .caseStmt _ items none _ _ => coreMemCaseBlockingWrites items
  | .caseStmt _ items (some defaultBody) _ _ =>
      coreMemCaseBlockingWrites items ++ coreMemStmtBlockingWrites defaultBody
  | .unsupported _ _ => []

def coreMemStmtBlockingWritesList : List PStmt → List String
  | [] => []
  | stmt :: rest =>
      coreMemStmtBlockingWrites stmt ++ coreMemStmtBlockingWritesList rest

def coreMemCaseBlockingWrites : List (List PExpr × PStmt) → List String
  | [] => []
  | item :: rest =>
      coreMemStmtBlockingWrites item.2 ++ coreMemCaseBlockingWrites rest

end

def coreMemProcWrites : PProcess → List String
  | .alwaysFF _ body | .alwaysFFNegedge _ body | .alwaysPlain _ body
  | .alwaysComb body | .alwaysLatch body | .alwaysImplicit body
  | .alwaysEvent _ body
  | .alwaysFFR _ _ body _ | .initial body => coreMemStmtWrites body
  | .assign _ _ | .assignL _ _ | .unsupported _ _ => []

def coreMemProcBlockingWrites : PProcess → List String
  | .alwaysFF _ body | .alwaysFFNegedge _ body | .alwaysPlain _ body
  | .alwaysComb body | .alwaysLatch body | .alwaysImplicit body
  | .alwaysEvent _ body
  | .alwaysFFR _ _ body _ | .initial body => coreMemStmtBlockingWrites body
  | .assign _ _ | .assignL _ _ | .unsupported _ _ => []

def coreMemEventSources : List PProcess → List String
  | [] => []
  | .alwaysFF clock _ :: rest => clock :: coreMemEventSources rest
  | .alwaysFFNegedge clock _ :: rest => clock :: coreMemEventSources rest
  | .alwaysPlain clock _ :: rest => clock :: coreMemEventSources rest
  | .alwaysFFR clock reset _ _ :: rest =>
      clock :: reset :: coreMemEventSources rest
  | .alwaysEvent events _ :: rest =>
      events.map (·.signal) ++ coreMemEventSources rest
  | _ :: rest => coreMemEventSources rest

def coreMemWritesNameTwice (name : String) (writes : List String) : Bool :=
  (writes.filter (· == name)).length > 1

def coreMemSourceWrittenTwiceInBody (name : String) : List PProcess → Bool
  | [] => false
  | p :: rest =>
      coreMemWritesNameTwice name (coreMemProcWrites p) ||
        coreMemSourceWrittenTwiceInBody name rest

def coreMemSourceHasBlockingWrite (name : String) : List PProcess → Bool
  | [] => false
  | p :: rest =>
      (coreMemProcBlockingWrites p).contains name ||
        coreMemSourceHasBlockingWrite name rest

def coreMemFirstRepeatedEventSource : List String → List PProcess → Option String
  | [], _ => none
  | source :: rest, processes =>
      if coreMemSourceWrittenTwiceInBody source processes then some source
      else coreMemFirstRepeatedEventSource rest processes

def coreMemEventSourceMultiWriteViol (d : PDesign) (generated : List PProcess) :
    Option (String × String) :=
  let processes := d.processes ++ generated
  match coreMemFirstRepeatedEventSource (coreMemEventSources processes) processes with
  | none => none
  | some source =>
      if coreMemSourceHasBlockingWrite source processes then
        some ("Event:multiple-write",
          s!"4.3/10.4.1: blocking event source '{source}' is written more than once in one process activation; intermediate update events are not modeled")
      else
        some ("Event:multiple-write",
          s!"4.6: NBA event source '{source}' is written more than once in one process activation; intermediate update events are not modeled")

/-! Canonical E uses one explicit settled start state for every fixture: all
declaration initializers and input values are installed, then continuous
assignments settle, before the first cycle.  IEEE 1800-2023 §9.2.2.2 runs an
`always_comb` once at time zero, and §9.6 runs runtime `initial` processes; if
either (or an `always_latch`) drives an edge source, that time-zero event is
outside this start-state discipline.  Refuse the syntactic shape until the
scheduler models the time-zero activation exactly. -/

def coreMemTimeZeroProcWrites : PProcess → List String
  | .alwaysComb body | .alwaysLatch body | .initial body => coreMemStmtWrites body
  | _ => []

def coreMemTimeZeroSourceWrites : PProcess → List String
  | .assign target _ => [target]
  | .assignL (.ident target) _ => [target]
  | p => coreMemTimeZeroProcWrites p

def coreMemSourceWrittenAtTimeZero (name : String) : List PProcess → Bool
  | [] => false
  | p :: rest =>
      (coreMemTimeZeroSourceWrites p).contains name ||
        coreMemSourceWrittenAtTimeZero name rest

def coreMemFirstTimeZeroEventSource (sources : List String) (processes : List PProcess) :
    Option String :=
  match sources with
  | [] => none
  | source :: rest =>
      if coreMemSourceWrittenAtTimeZero source processes then some source
      else coreMemFirstTimeZeroEventSource rest processes

def coreMemTimeZeroEventSourceViol (d : PDesign) (generated : List PProcess) :
    Option (String × String) :=
  let processes := d.processes ++ generated
  match coreMemFirstRepeatedEventSource (coreMemEventSources processes) processes with
  | some source =>
      if coreMemSourceWrittenAtTimeZero source processes then
        some ("Event:time-zero",
          s!"4.7/9.4.2: event source '{source}' is driven by an initial/always_comb/always_latch or continuous-assign activation at time zero; canonical E refuses the unresolved scheduling race")
      else none
  | none =>
      match coreMemFirstTimeZeroEventSource (coreMemEventSources processes) processes with
      | none => none
      | some source =>
          some ("Event:time-zero",
            s!"4.7/9.4.2: event source '{source}' is driven by an initial/always_comb/always_latch or continuous-assign activation at time zero; canonical E refuses the unresolved scheduling race")

def coreMemClockResetViol (_d : PDesign) (_generated : List PProcess) :
    Option (String × String) :=
  -- Canonical E now iterates NBA-caused clock/reset events in the same slot
  -- (§§4.4, 4.5); the ordinary run2 loader keeps its separate discipline guard.
  none

/-! Module-level metadata that is already represented by retained source nodes.
An empty input-only task has no runtime effect, and the two x/z markers carry
the literal as a source `PExpr.lit`; admitting these markers therefore does not
invent a process or a value.  An undriven four-state wire is admitted only
from the structured Slang metadata: IEEE 1800-2023 §6.6 gives every bit its z
startup value, while the absence of driver records means no resolution rule is
being inferred.  Other net shapes remain loud. -/

def coreMemAllowedOther (entry : String × String) : Bool :=
  entry.1 == "SubroutineSymbol:empty-task" ||
    entry.1 == "IntegerLiteral:unsized-xz-parametric" ||
    entry.1 == "ConversionExpression:xz-literal-parametric"

def coreMemNetMetadataAllowed (md : PNetMetadata) : Bool :=
  md.netKind == "Wire" && md.isNet && md.fourState && !md.signed &&
    md.driverReason == some "no driver: the net reads z" && md.driverRecords.isEmpty && md.width > 0

def coreMemNetDriverAllowed (md : PNetMetadata) (generated : List PProcess) : Bool :=
  !md.driverRecords.isEmpty &&
    md.driverRecords.all (fun r =>
      r.bounds == (0, Int.ofNat md.width - 1) &&
        r.ownerKind == "ContinuousAssignSymbol" && r.generated && r.source == md.name) &&
    generated.any (fun p => match p with
      | .assign target _ => target == md.name
      | .assignL (.ident target) _ => target == md.name
      | _ => false)

def coreMemResolvedNetNames (d : PDesign) (generated : List PProcess) : List String :=
  d.netMetadata.filterMap fun md =>
    if md.driverRecords.length > 1 && coreMemNetDriverAllowed md generated then some md.name else none

def coreMemNetAllowed (d : PDesign) (generated : List PProcess) (kind name : String) : Bool :=
  d.others.any (fun entry => entry.1 == kind && entry.2 == name) &&
    d.netMetadata.any (fun md => md.name == name &&
      (coreMemNetMetadataAllowed md || coreMemNetDriverAllowed md generated ||
       (d.primitives.any (fun p => p.target.name == name))))

/-! A generated net marker lives in `GenItem`, rather than `PDesign.others`.
The parser-native metadata is retained on the design above, and the marker is
admitted only when that metadata proves either an undriven four-state net or a
single generated continuous driver.  The latter check is against the fully
expanded source-shaped process list, so a marker cannot silently erase a net
whose driver was not retained.  IEEE 1800-2023 §§6.6 and 27.4. -/
def coreMemGeneratedNetAllowed (d : PDesign) (generated : List PProcess)
    (kind name : String) : Bool :=
  (kind == "NetSymbol:net-z" || kind == "PortSymbol:net-z") &&
    d.netMetadata.any (fun md => md.name == name &&
      (coreMemNetMetadataAllowed md || coreMemNetDriverAllowed md generated))

def coreMemDropGeneratedNetMarkers (d : PDesign) (generated : List PProcess) : List PProcess :=
  generated.filter fun p =>
    match p with
    | .unsupported kind name => !coreMemGeneratedNetAllowed d generated kind name
    | _ => true

def coreMemMetadataIsOutput (d : PDesign) (name : String) : Bool :=
  d.others.any fun entry => entry.1 == "PortSymbol:net-z" && entry.2 == name

def coreMemFirstUnsupportedOther (d : PDesign) (generated : List PProcess) : List (String × String) → Option (String × String)
  | [] => none
  | entry :: rest =>
      if coreMemAllowedOther entry ||
          ((entry.1 == "NetSymbol:net-z" || entry.1 == "PortSymbol:net-z") &&
            coreMemNetAllowed d generated entry.1 entry.2) then
        coreMemFirstUnsupportedOther d generated rest
      else some entry

def coreMemNetDecls (d : PDesign) (generated : List PProcess) : List Decl :=
  d.netMetadata.filter (fun md => !md.generated) |>.filterMap fun md =>
    if coreMemNetMetadataAllowed md || coreMemNetDriverAllowed md generated ||
        d.primitives.any (fun p => p.target.name == md.name) then
      let dc : Decl := { name := md.name, width := md.width, isOutput := coreMemMetadataIsOutput d md.name, isNet := true, init := some (LVec.replicate md.width .lz) }
      some dc
    else none

def coreMemMetadataType (md : PNetMetadata) : PType :=
  if md.width == 1 then .packed [] (some 1)
  else .packed [⟨.int (Int.ofNat md.width - 1), .int 0⟩] (some md.width)

def coreMemMetadataDecl (md : PNetMetadata) : PDecl :=
  { name := md.name, type := coreMemMetadataType md, isSigned := md.signed,
    twoState := !md.fourState, isNet := md.isNet }

def coreMemMetadataDecls : List PNetMetadata → List PDecl
  | [] => []
  | md :: rest => coreMemMetadataDecl md :: coreMemMetadataDecls rest

/-! ## Source-shaped generate expansion

Generate elaboration selects and repeats the parser's process nodes; it does
not lower their bodies into `Process2` or expand memory declarations into
cells. A concrete genvar is retained as an integer expression in the copied
source node, so the canonical executor still sees the original `PProcess` /
`PStmt` shape and the native `MemState` route.
-/

/-! The lexical constants active while walking one generate instance.  Genvars
and generate-local parameters are kept separately so a genvar has the
shadowing priority required by IEEE 1800 section 27.4. -/
structure CoreMemScope where
  genvars : List (String × Int) := []
  localParams : List (String × Int) := []
  /-- Non-INT generate-local constants retain their declared width and
  signedness while their lexical scope is substituted. -/
  localNParams : List (String × (Int × Nat × Bool)) := []
deriving Repr, Inhabited

def coreMemScopeEnv (env : IEnv) (scope : CoreMemScope) : IEnv :=
  let env := scope.localParams.reverse.foldl
    (fun e (n, v) => e.bindVal n v) env
  let env := scope.localNParams.reverse.foldl
    (fun e (n, (v, w, s)) => e.bindNVal n v w s) env
  scope.genvars.reverse.foldl (fun e (n, v) => e.bindVal n v) env

/-! Evaluate a generate-local parameter in the active lexical scope.  The
canonical memory executor carries integer constants across generated
source-shaped nodes and preserves the declared width and signedness of a
non-INT constant. IEEE 1800-2023 §§6.20.2 and 27.4. -/
def coreMemBindLocalParam (env : IEnv) (scope : CoreMemScope) (p : PLocalParam) :
    Res CoreMemScope :=
  match bindLocal (coreMemScopeEnv env scope) p with
  | .error e => .unsupported
      s!"GenerateDecl:LocalParam: generate-local parameter '{p.name}': {e}"
  | .ok env' =>
      match env'.intVal? p.name with
      | some v => .ok { scope with localParams := (p.name, v) :: scope.localParams }
      | none =>
          match env'.nvals.lookup p.name with
          | some (v, w, s) =>
              .ok { scope with localNParams := (p.name, (v, w, s)) :: scope.localNParams }
          | none => .unsupported
              s!"GenerateDecl:LocalParam: generate-local parameter '{p.name}': non-INT type is outside the canonical E scope"

def coreMemSubstExpr (scope : CoreMemScope) : PExpr → PExpr
  | .genvarRef n =>
      match scope.genvars.lookup n with
      | some v => .int v
      | none => .genvarRef n
  | .paramRef n none =>
      match scope.localParams.lookup n with
      | some v => .int v
      | none =>
          match scope.localNParams.lookup n with
          | some (v, w, s) =>
              if s then .signedResize w (.lit (.ofInt w v))
              else .lit (.ofInt w v)
          | none => .paramRef n none
  | .unary op a => .unary op (coreMemSubstExpr scope a)
  | .binary op a b => .binary op (coreMemSubstExpr scope a) (coreMemSubstExpr scope b)
  | .ternary c a b => .ternary (coreMemSubstExpr scope c) (coreMemSubstExpr scope a)
      (coreMemSubstExpr scope b)
  | .concat xs => .concat (xs.map (coreMemSubstExpr scope))
  | .resize w a => .resize w (coreMemSubstExpr scope a)
  | .signedResize w a => .signedResize w (coreMemSubstExpr scope a)
  | .squash2 w a => .squash2 w (coreMemSubstExpr scope a)
  | .sysCall fn a => .sysCall fn (coreMemSubstExpr scope a)
  | .bitSel a b => .bitSel (coreMemSubstExpr scope a) (coreMemSubstExpr scope b)
  | .partSel a b c => .partSel (coreMemSubstExpr scope a) (coreMemSubstExpr scope b)
      (coreMemSubstExpr scope c)
  | .repl a b => .repl (coreMemSubstExpr scope a) (coreMemSubstExpr scope b)
  | .reduce op a => .reduce op (coreMemSubstExpr scope a)
  | .cast s a => .cast s (coreMemSubstExpr scope a)
  | .arrayElem n xs => .arrayElem n (xs.map (coreMemSubstExpr scope))
  | .arrayPart n xs mode a b => .arrayPart n (xs.map (coreMemSubstExpr scope)) mode
      (coreMemSubstExpr scope a) (coreMemSubstExpr scope b)
  | .functionCall n xs => .functionCall n (xs.map (coreMemSubstExpr scope))
  | e => e

def coreMemSubstLhs (scope : CoreMemScope) : PLhs → PLhs
  | .bitSel n i => .bitSel n (coreMemSubstExpr scope i)
  | .partSel n a b => .partSel n (coreMemSubstExpr scope a) (coreMemSubstExpr scope b)
  | .concat xs => .concat (xs.map (coreMemSubstLhs scope))
  | .arrayElem n xs => .arrayElem n (xs.map (coreMemSubstExpr scope))
  | .arrayPart n xs mode a b => .arrayPart n (xs.map (coreMemSubstExpr scope)) mode
      (coreMemSubstExpr scope a) (coreMemSubstExpr scope b)
  | l => l

def coreMemSubstDim (scope : CoreMemScope) (d : PDim) : PDim :=
  { msb := coreMemSubstExpr scope d.msb, lsb := coreMemSubstExpr scope d.lsb }

def coreMemSubstType (scope : CoreMemScope) : PType → PType
  | .packed dims resolved => .packed (dims.map (coreMemSubstDim scope)) resolved
  | .typeRef n pkg resolved => .typeRef n pkg resolved
  | .unrecoverable resolved => .unrecoverable resolved

def coreMemSubstDecl (scope : CoreMemScope) (d : PDecl) : PDecl :=
  { name := d.name, type := coreMemSubstType scope d.type,
    unpackedDims := d.unpackedDims.map (coreMemSubstDim scope),
    isSigned := d.isSigned, twoState := d.twoState, isInput := d.isInput,
    isOutput := d.isOutput, isNet := d.isNet,
    init := d.init.map (coreMemSubstExpr scope), flatBase := d.flatBase,
    flatIndex := d.flatIndex }

mutual
def coreMemSubstStmt (scope : CoreMemScope) : PStmt → PStmt
  | .blockingAssign n e => .blockingAssign n (coreMemSubstExpr scope e)
  | .nbaAssign n e => .nbaAssign n (coreMemSubstExpr scope e)
  | .ifStmt c t e => .ifStmt (coreMemSubstExpr scope c) (coreMemSubstStmt scope t)
      (coreMemSubstStmtOpt scope e)
  | .block xs => .block (coreMemSubstStmtList scope xs)
  | .forLoop n i c s b => .forLoop n (coreMemSubstExpr scope i)
      (coreMemSubstExpr scope c) (coreMemSubstExpr scope s) (coreMemSubstStmt scope b)
  | .blockingAssignL l e => .blockingAssignL (coreMemSubstLhs scope l)
      (coreMemSubstExpr scope e)
  | .nbaAssignL l e => .nbaAssignL (coreMemSubstLhs scope l)
      (coreMemSubstExpr scope e)
  | .caseStmt s items d mode check =>
      .caseStmt (coreMemSubstExpr scope s)
        (coreMemSubstCaseItems scope items) (coreMemSubstStmtOpt scope d) mode check
  | s => s
termination_by structural s => s

def coreMemSubstStmtOpt (scope : CoreMemScope) : Option PStmt → Option PStmt
  | none => none
  | some s => some (coreMemSubstStmt scope s)
termination_by structural o => o

def coreMemSubstStmtList (scope : CoreMemScope) : List PStmt → List PStmt
  | [] => []
  | s :: ss => coreMemSubstStmt scope s :: coreMemSubstStmtList scope ss
termination_by structural xs => xs

def coreMemSubstCaseItems (scope : CoreMemScope) :
    List (List PExpr × PStmt) → List (List PExpr × PStmt)
  | [] => []
  | (ps, b) :: rest =>
      (ps.map (coreMemSubstExpr scope), coreMemSubstStmt scope b) ::
        coreMemSubstCaseItems scope rest
termination_by structural xs => xs

def coreMemSubstProcess (scope : CoreMemScope) : PProcess → PProcess
  | .alwaysFF c b => .alwaysFF c (coreMemSubstStmt scope b)
  | .alwaysFFNegedge c b => .alwaysFFNegedge c (coreMemSubstStmt scope b)
  | .alwaysPlain c b => .alwaysPlain c (coreMemSubstStmt scope b)
  | .alwaysComb b => .alwaysComb (coreMemSubstStmt scope b)
  | .alwaysLatch b => .alwaysLatch (coreMemSubstStmt scope b)
  | .alwaysImplicit b => .alwaysImplicit (coreMemSubstStmt scope b)
  | .alwaysEvent events b => .alwaysEvent events (coreMemSubstStmt scope b)
  | .assign n e => .assign n (coreMemSubstExpr scope e)
  | .assignL l e => .assignL (coreMemSubstLhs scope l) (coreMemSubstExpr scope e)
  | .alwaysFFR c r b h => .alwaysFFR c r (coreMemSubstStmt scope b) h
  | .initial b => .initial (coreMemSubstStmt scope b)
  | p => p
end

def coreMemBindVals (env : IEnv) (scope : CoreMemScope) : IEnv :=
  let env := scope.localParams.reverse.foldl
    (fun e (n, v) => e.bindVal n v) env
  let env := scope.localNParams.reverse.foldl
    (fun e (n, (v, w, s)) => e.bindNVal n v w s) env
  scope.genvars.reverse.foldl (fun e (n, v) => e.bindVal n v) env

/-! Active generated declarations are collected from the same source-shaped
walk as generated processes.  A declaration is copied once for each active
generate instance, with genvar references substituted in its dimensions;
inactive branches are never visited.  This is the declaration half of IEEE
1800-2023 §§27.4/27.5 and deliberately does not lower a declaration to cells.
-/

mutual
def coreMemGeneratedDeclsItem (env : IEnv) (iterFuel : Nat)
    (scope : CoreMemScope) : GenItem → Res (List PDecl)
  | .process _ | .unsupported _ _ | .inst _ => .ok []
  | .decl d => .ok [coreMemSubstDecl scope d]
  | .localParam _ => .ok []
  | .genIf cond thenB elseB =>
      match evalGenGuard (coreMemBindVals env scope) cond with
      | .error e => .unsupported s!"generate if: {e}"
      | .ok v =>
          if v != 0 then
            do
              let (ds, _) ← coreMemGeneratedDeclsList env iterFuel scope thenB
              pure ds
          else
            do
              let (ds, _) ← coreMemGeneratedDeclsList env iterFuel scope elseB
              pure ds
  | .genFor _label g initE bound step _rc body =>
      let env' := coreMemBindVals env scope
      match evalInt env' initE, stepDelta g step with
      | .ok i0, .ok δ => do
          let vs ← genvarSeq env' g bound δ iterFuel i0
          coreMemGeneratedDeclsIters env iterFuel scope g vs body
      | .error e, _ => .unsupported s!"generate for: {e}"
      | _, .error e => .unsupported s!"generate for: {e}"
  termination_by it => (sizeOf it, 0)
  decreasing_by all_goals (simp_wf; omega)

def coreMemGeneratedDeclsList (env : IEnv) (iterFuel : Nat)
    (scope : CoreMemScope) : List GenItem → Res (List PDecl × CoreMemScope)
  | [] => .ok ([], scope)
  | .localParam p :: rest => do
      let scope' ← coreMemBindLocalParam env scope p
      coreMemGeneratedDeclsList env iterFuel scope' rest
  | it :: rest => do
      let ds ← coreMemGeneratedDeclsItem env iterFuel scope it
      let (tail, scope') ← coreMemGeneratedDeclsList env iterFuel scope rest
      .ok (ds ++ tail, scope')
  termination_by xs => (sizeOf xs, 0)
  decreasing_by all_goals (simp_wf; omega)

def coreMemGeneratedDeclsIters (env : IEnv) (iterFuel : Nat)
    (scope : CoreMemScope) (g : String) : List Int → List GenItem → Res (List PDecl)
  | [], _ => .ok []
  | v :: vs, body => do
      let scope' := { scope with genvars := (g, v) :: scope.genvars }
      let (ds, _) ← coreMemGeneratedDeclsList env iterFuel scope' body
      let tail ← coreMemGeneratedDeclsIters env iterFuel scope g vs body
      .ok (ds ++ tail)
  termination_by vs body => (sizeOf body, vs.length + 1)
  decreasing_by all_goals (simp_wf; omega)
end

def coreMemDeclNamesUnique (decls : List PDecl) : Bool :=
  let names := decls.map (fun d => d.name)
  names.eraseDups.length == names.length

mutual
def coreMemExpandItem (env : IEnv) (iterFuel : Nat) (scope : CoreMemScope) :
    GenItem → Res (List PProcess)
  | .process p => .ok [coreMemSubstProcess scope p]
  | .decl _ => .ok []
  | .localParam _ => .ok []
  | .unsupported k t => .ok [.unsupported k t]
  | .inst i => .ok [.unsupported "Instance"
      s!"module instance '{i.name}' of '{i.module}' outside the canonical E memory route"]
  | .genIf cond thenB elseB =>
      match evalGenGuard (coreMemBindVals env scope) cond with
      | .error e => .unsupported s!"generate if: {e}"
      | .ok v =>
          if v != 0 then
            do
              let (ps, _) ← coreMemExpandList env iterFuel scope thenB
              pure ps
          else
            do
              let (ps, _) ← coreMemExpandList env iterFuel scope elseB
              pure ps
  | .genFor _label g initE bound step _rc body =>
      let env' := coreMemBindVals env scope
      match evalInt env' initE, stepDelta g step with
      | .ok i0, .ok δ => do
          let vs ← genvarSeq env' g bound δ iterFuel i0
          coreMemExpandIters env iterFuel scope g vs body
      | .error e, _ => .unsupported s!"generate for: {e}"
      | _, .error e => .unsupported s!"generate for: {e}"
  termination_by it => (sizeOf it, 0)
  decreasing_by all_goals (simp_wf; omega)

def coreMemExpandList (env : IEnv) (iterFuel : Nat) (scope : CoreMemScope) :
    List GenItem → Res (List PProcess × CoreMemScope)
  | [] => .ok ([], scope)
  | .localParam p :: rest => do
      let scope' ← coreMemBindLocalParam env scope p
      coreMemExpandList env iterFuel scope' rest
  | it :: rest => do
      let ps ← coreMemExpandItem env iterFuel scope it
      let (qs, scope') ← coreMemExpandList env iterFuel scope rest
      .ok (ps ++ qs, scope')
  termination_by xs => (sizeOf xs, 0)
  decreasing_by all_goals (simp_wf; omega)

def coreMemExpandIters (env : IEnv) (iterFuel : Nat) (scope : CoreMemScope)
    (g : String) : List Int → List GenItem → Res (List PProcess)
  | [], _ => .ok []
  | v :: vs, body => do
      let scope' := { scope with genvars := (g, v) :: scope.genvars }
      let (ps, _) ← coreMemExpandList env iterFuel scope' body
      let qs ← coreMemExpandIters env iterFuel scope g vs body
      .ok (ps ++ qs)
  termination_by vs body => (sizeOf body, vs.length + 1)
  decreasing_by all_goals (simp_wf; omega)
end

/-! A continuous-assignment pass is source ordered.  IEEE 1800-2023
§4.5/§10.3 requires the slot to remain active until every driver is current;
the present E route uses one pass, so it admits only the sufficient
topological-source-order shape.  Keep this check on the retained `PExpr` /
`PLhs` nodes: it is an admission guard, not a lowering of the source. -/
mutual
def coreMemSignalNames : PExpr → List String
  | .ident n => [n]
  | .arrayElem n is => n :: coreMemSignalNamesList is
  | .arrayPart n is _ a b => n :: (coreMemSignalNamesList is ++ coreMemSignalNames a ++ coreMemSignalNames b)
  | .unary _ a | .resize _ a | .signedResize _ a | .squash2 _ a
  | .sysCall _ a | .reduce _ a | .cast _ a => coreMemSignalNames a
  | .binary _ a b | .bitSel a b | .repl a b => coreMemSignalNames a ++ coreMemSignalNames b
  | .ternary c a b | .partSel c a b =>
      coreMemSignalNames c ++ coreMemSignalNames a ++ coreMemSignalNames b
  | .concat xs | .functionCall _ xs => coreMemSignalNamesList xs
  | .aggregateMember n _ => [n]
  | .packageAggElem pkg n index => (pkg ++ "::" ++ n) :: coreMemSignalNames index
  | .lit _ | .paramRef _ _ | .genvarRef _ | .enumRef _ _ _ | .int _ | .fill _
  | .typeBits ..
  | .unsupported _ _ => []

def coreMemSignalNamesList : List PExpr → List String
  | [] => []
  | x :: xs => coreMemSignalNames x ++ coreMemSignalNamesList xs
end

def coreMemLhsTargets : PLhs → List String
  | .ident n | .bitSel n _ | .partSel n _ _ | .arrayElem n _ | .arrayPart n .. => [n]
  | .aggregateMember n _ => [n]
  | .concat xs => xs.flatMap coreMemLhsTargets

def coreMemAssignTargets : List CoreMemProc → List String
  | [] => []
  | .assign target _ :: rest => coreMemLhsTargets target ++ coreMemAssignTargets rest
  | _ :: rest => coreMemAssignTargets rest

def coreMemAssignTopoB : List CoreMemProc → Bool
  | [] => true
  | p :: rest =>
      (match p with
       | .assign _ value =>
           (coreMemSignalNames value).all fun name =>
             !(coreMemAssignTargets (p :: rest)).contains name
       | _ => true) && coreMemAssignTopoB rest

def CoreMemDesign.assignTopoB (E : CoreMemDesign) : Bool :=
  coreMemAssignTopoB E.processes.toList

mutual
def coreMemPExprHasMemory : PExpr → Bool
  | .arrayElem .. | .arrayPart .. => true
  | .aggregateMember .. | .packageAggElem .. => true
  | .unary _ a | .resize _ a | .signedResize _ a | .squash2 _ a
  | .sysCall _ a | .reduce _ a | .cast _ a => coreMemPExprHasMemory a
  | .binary _ a b => coreMemPExprHasMemory a || coreMemPExprHasMemory b
  | .ternary c a b => coreMemPExprHasMemory c || coreMemPExprHasMemory a || coreMemPExprHasMemory b
  | .concat xs | .functionCall _ xs => coreMemPExprHasMemoryList xs
  | .bitSel a b | .repl a b => coreMemPExprHasMemory a || coreMemPExprHasMemory b
  | .partSel a b c => coreMemPExprHasMemory a || coreMemPExprHasMemory b || coreMemPExprHasMemory c
  | .lit _ | .ident _ | .paramRef .. | .genvarRef _ | .enumRef .. | .int _
  | .typeBits .. | .fill _ | .unsupported .. => false

def coreMemPExprHasMemoryList : List PExpr → Bool
  | [] => false
  | x :: xs => coreMemPExprHasMemory x || coreMemPExprHasMemoryList xs

end

mutual
def coreMemPLhsHasMemory : PLhs → Bool
  | .arrayElem .. | .arrayPart .. => true
  | .aggregateMember .. => true
  | .bitSel _ i => coreMemPExprHasMemory i
  | .partSel _ msb lsb => coreMemPExprHasMemory msb || coreMemPExprHasMemory lsb
  | .concat xs => coreMemPLhsHasMemoryList xs
  | .ident _ => false

def coreMemPLhsHasMemoryList : List PLhs → Bool
  | [] => false
  | x :: xs => coreMemPLhsHasMemory x || coreMemPLhsHasMemoryList xs

end

def coreMemPAssignTarget : PProcess → Option String
  | .assign target _ => some target
  | .assignL target _ => some target.name
  | _ => none

def coreMemPAssignValue : PProcess → Option PExpr
  | .assign _ value | .assignL _ value => some value
  | _ => none

def coreMemPAssignUsesMemory : PProcess → Bool
  | .assignL target value => coreMemPLhsHasMemory target || coreMemPExprHasMemory value
  | .assign _ value => coreMemPExprHasMemory value
  | _ => false

def coreMemPAssignTargets : List PProcess → List String
  | [] => []
  | p :: rest => (match coreMemPAssignTarget p with | some name => [name] | none => []) ++
      coreMemPAssignTargets rest

def coreMemPAssignMemoryTopoB : List PProcess → Bool
  | [] => true
  | p :: rest =>
      match coreMemPAssignTarget p, coreMemPAssignValue p with
      | some target, some value =>
          let laterTargets := coreMemPAssignTargets (p :: rest)
          let backward := (coreMemSignalNames value).any (fun name => laterTargets.contains name)
          (!coreMemPAssignUsesMemory p || !backward) && coreMemPAssignMemoryTopoB rest
      | _, _ => coreMemPAssignMemoryTopoB rest

def coreMemHasEdgeProc : List PProcess → Bool
  | [] => false
  | p :: rest =>
      (match p with
       | .alwaysFF .. | .alwaysFFNegedge .. | .alwaysPlain .. | .alwaysFFR .. => true
       | _ => false) || coreMemHasEdgeProc rest

/-! Comb/latch/implicit bodies are activated after the edge pass, but this
executor does not yet run a dependency scheduler to a fixed point.  Therefore
admit only a source-order topological fragment: a reactive process may not
read a signal written by itself or by a later reactive process.  A later
writer is the syntactic witness of a backward dependency (and a mutual pair
is a cycle).  Continuous assignments are excluded from this guard because
`settleCanonical` evaluates their scalar layer before reactive bodies; the
memory-assignment boundary is handled separately. -/

mutual

def coreMemStmtReadNames : PStmt → List String
  | .localDecl _ _ init => init.toList.flatMap coreMemSignalNames
  | .automaticDecl _ _ init => init.toList.flatMap coreMemSignalNames
  | .blockingAssign _ value | .nbaAssign _ value => coreMemSignalNames value
  | .blockingAssignL target value | .nbaAssignL target value =>
      coreMemLhsReadNames target ++ coreMemSignalNames value
  | .ifStmt cond yes none => coreMemSignalNames cond ++ coreMemStmtReadNames yes
  | .ifStmt cond yes (some no) =>
      coreMemSignalNames cond ++ coreMemStmtReadNames yes ++ coreMemStmtReadNames no
  | .block body => coreMemStmtReadNamesList body
  | .forLoop _ initE condition step body =>
      coreMemSignalNames initE ++ coreMemSignalNames condition ++
        coreMemSignalNames step ++ coreMemStmtReadNames body
  | .caseStmt subject items none _ _ =>
      coreMemSignalNames subject ++ coreMemCaseReadNames items
  | .caseStmt subject items (some defaultBody) _ _ =>
      coreMemSignalNames subject ++ coreMemCaseReadNames items ++
        coreMemStmtReadNames defaultBody
  | .unsupported _ _ => []

def coreMemStmtReadNamesList : List PStmt → List String
  | [] => []
  | stmt :: rest => coreMemStmtReadNames stmt ++ coreMemStmtReadNamesList rest

def coreMemCaseReadNames : List (List PExpr × PStmt) → List String
  | [] => []
  | item :: rest =>
      coreMemSignalNamesList item.1 ++ coreMemStmtReadNames item.2 ++
        coreMemCaseReadNames rest

def coreMemLhsReadNames : PLhs → List String
  | .ident _ => []
  | .bitSel _ index => coreMemSignalNames index
  | .partSel _ msb lsb => coreMemSignalNames msb ++ coreMemSignalNames lsb
  | .concat parts => coreMemLhsReadNamesList parts
  | .arrayElem _ indices | .arrayPart _ indices .. => coreMemSignalNamesList indices
  | .aggregateMember _ path =>
      (path.filterMap (fun step => step.2)).flatMap coreMemSignalNames

def coreMemLhsReadNamesList : List PLhs → List String
  | [] => []
  | lhs :: rest => coreMemLhsReadNames lhs ++ coreMemLhsReadNamesList rest

end

def coreMemPProcessEdgeSources : PProcess → List String
  | .alwaysFF clock _ | .alwaysFFNegedge clock _ | .alwaysPlain clock _ => [clock]
  | .alwaysFFR clock reset _ _ => [clock, reset]
  | .alwaysEvent events _ => events.map (·.signal)
  | _ => []

def coreMemPProcessReadNames : PProcess → List String
  | .alwaysFF _ body | .alwaysFFNegedge _ body | .alwaysPlain _ body
  | .alwaysFFR _ _ body _ | .alwaysEvent _ body => coreMemStmtReadNames body
  | _ => []

def coreMemHasCommonEventSource (p q : PProcess) : Bool :=
  (coreMemPProcessEdgeSources p).any (fun source =>
    (coreMemPProcessEdgeSources q).contains source)

def coreMemEdgeBlockingReadRacePair (p q : PProcess) : Bool :=
  coreMemHasCommonEventSource p q &&
    ((coreMemProcBlockingWrites p).any (fun name =>
      (coreMemPProcessReadNames q).contains name) ||
     (coreMemProcBlockingWrites q).any (fun name =>
      (coreMemPProcessReadNames p).contains name))

def coreMemEdgeBlockingReadRaceAt (p : PProcess) : List PProcess → Bool
  | [] => false
  | q :: rest =>
      coreMemEdgeBlockingReadRacePair p q || coreMemEdgeBlockingReadRaceAt p rest

def coreMemEdgeBlockingReadRace : List PProcess → Bool
  | [] | [_] => false
  | p :: rest => coreMemEdgeBlockingReadRaceAt p rest || coreMemEdgeBlockingReadRace rest

def coreMemEdgeBlockingReadRaceViol (d : PDesign) (generated : List PProcess) :
    Option (String × String) :=
  let edgeProcesses := (d.processes ++ generated).filter
    (fun p => !(coreMemPProcessEdgeSources p).isEmpty)
  if coreMemEdgeBlockingReadRace edgeProcesses then
    some ("Event:edge-blocking-race",
      "4.7/10.4.1: same-edge blocking read/write processes have schedule-dependent visibility; canonical E refuses the race")
  else none

/-! A reactive body may read a signal that it assigned earlier in the same
process.  That sequential source order is defined by IEEE 1800-2023 §9.2.2.2
and does not create an inter-process scheduling cycle.  Keep only reads that
occur before the body's first write to the same name when checking the
cross-process dependency guard. -/

mutual

def coreMemStmtReadBeforeWritesFrom (written : List String) : PStmt → List String × List String
  | .localDecl name _ init =>
      ((init.toList.flatMap coreMemSignalNames).filter (fun n => !written.contains n), name :: written)
  | .automaticDecl _ _ init =>
      ((init.toList.flatMap coreMemSignalNames).filter (fun n => !written.contains n), written)
  | .blockingAssign name value | .nbaAssign name value =>
      ((coreMemSignalNames value).filter (fun n => !written.contains n), name :: written)
  | .blockingAssignL target value | .nbaAssignL target value =>
      let reads := coreMemLhsReadNames target ++ coreMemSignalNames value
      (reads.filter (fun n => !written.contains n), target.name :: written)
  | .ifStmt cond yes none =>
      let condReads := (coreMemSignalNames cond).filter (fun n => !written.contains n)
      let (yesReads, yesWrites) := coreMemStmtReadBeforeWritesFrom written yes
      (condReads ++ yesReads, yesWrites)
  | .ifStmt cond yes (some no) =>
      let condReads := (coreMemSignalNames cond).filter (fun n => !written.contains n)
      let (yesReads, yesWrites) := coreMemStmtReadBeforeWritesFrom written yes
      let (noReads, noWrites) := coreMemStmtReadBeforeWritesFrom written no
      (condReads ++ yesReads ++ noReads, yesWrites ++ noWrites)
  | .block body => coreMemStmtReadBeforeWritesListFrom written body
  | .forLoop _ initE condition step body =>
      let initReads := (coreMemSignalNames initE).filter (fun n => !written.contains n)
      let condReads := (coreMemSignalNames condition).filter (fun n => !written.contains n)
      let stepReads := (coreMemSignalNames step).filter (fun n => !written.contains n)
      let (bodyReads, bodyWrites) := coreMemStmtReadBeforeWritesFrom written body
      (initReads ++ condReads ++ stepReads ++ bodyReads, bodyWrites)
  | .caseStmt subject items none _ _ =>
      let subjectReads := (coreMemSignalNames subject).filter (fun n => !written.contains n)
      let itemReads := coreMemCaseReadBeforeWritesFrom written items
      (subjectReads ++ itemReads.1, itemReads.2)
  | .caseStmt subject items (some defaultBody) _ _ =>
      let subjectReads := (coreMemSignalNames subject).filter (fun n => !written.contains n)
      let itemReads := coreMemCaseReadBeforeWritesFrom written items
      let (defaultReads, defaultWrites) := coreMemStmtReadBeforeWritesFrom written defaultBody
      (subjectReads ++ itemReads.1 ++ defaultReads, itemReads.2 ++ defaultWrites)
  | .unsupported _ _ => ([], written)

def coreMemStmtReadBeforeWritesListFrom (written : List String) : List PStmt → List String × List String
  | [] => ([], written)
  | stmt :: rest =>
      let (reads, written') := coreMemStmtReadBeforeWritesFrom written stmt
      let (restReads, restWritten) := coreMemStmtReadBeforeWritesListFrom written' rest
      (reads ++ restReads, restWritten)

def coreMemCaseReadBeforeWritesFrom (written : List String) :
    List (List PExpr × PStmt) → List String × List String
  | [] => ([], written)
  | item :: rest =>
      let patternReads := (coreMemSignalNamesList item.1).filter (fun n => !written.contains n)
      let (bodyReads, bodyWrites) := coreMemStmtReadBeforeWritesFrom written item.2
      let (restReads, restWrites) := coreMemCaseReadBeforeWritesFrom written rest
      (patternReads ++ bodyReads ++ restReads, bodyWrites ++ restWrites)

end

def coreMemReactiveReadBeforeWrites : PProcess → List String
  | .alwaysComb body | .alwaysLatch body | .alwaysImplicit body =>
      (coreMemStmtReadBeforeWritesFrom [] body).1
  | _ => []

def coreMemReactiveProc : PProcess → Bool
  | .alwaysComb _ | .alwaysLatch _ | .alwaysImplicit _ => true
  | _ => false

def coreMemReactiveWrites : PProcess → List String
  | .alwaysComb body | .alwaysLatch body | .alwaysImplicit body => coreMemStmtWrites body
  | _ => []

/-! `always_comb` and `always_latch` are settled together by the canonical
quiescence pass below. A continuous assignment between two such activations
therefore remains source-shaped and executable. Plain implicit-event bodies
run in the separate Active-region pass, so a reactive-to-assignment-to-implicit
chain remains outside this zero-delay profile. -/
def coreMemSeparateReactiveProc : PProcess → Bool
  | .alwaysImplicit _ => true
  | _ => false

def coreMemReactiveReads : PProcess → List String
  | .alwaysComb body | .alwaysLatch body | .alwaysImplicit body => coreMemStmtReadNames body
  | _ => []

/-! Static block-local declarations are allocated in the same scalar store as
their enclosing process. Automatic declarations stay in the activation-local
environment and are therefore absent from this design-level declaration list. -/
mutual
def coreMemLocalDeclsStmt : PStmt → List PDecl
  | .localDecl name width init =>
      [{ name,
         type := .packed [{ msb := .int (Int.ofNat (width - 1)),
                            lsb := .int 0 }] (some width),
         init }]
  | .automaticDecl _ _ _ => []
  | .block body => coreMemLocalDeclsList body
  | .ifStmt _ yes none => coreMemLocalDeclsStmt yes
  | .ifStmt _ yes (some no) => coreMemLocalDeclsStmt yes ++ coreMemLocalDeclsStmt no
  | .forLoop _ _ _ _ body => coreMemLocalDeclsStmt body
  | .caseStmt _ items none _ _ => coreMemLocalDeclsCase items
  | .caseStmt _ items (some defaultBody) _ _ =>
      coreMemLocalDeclsCase items ++ coreMemLocalDeclsStmt defaultBody
  | _ => []

def coreMemLocalDeclsList : List PStmt → List PDecl
  | [] => []
  | stmt :: rest => coreMemLocalDeclsStmt stmt ++ coreMemLocalDeclsList rest

def coreMemLocalDeclsCase : List (List PExpr × PStmt) → List PDecl
  | [] => []
  | item :: rest => coreMemLocalDeclsStmt item.2 ++ coreMemLocalDeclsCase rest

def coreMemLocalDeclsProc : PProcess → List PDecl
  | .alwaysFF _ body | .alwaysFFNegedge _ body | .alwaysPlain _ body
  | .alwaysComb body | .alwaysLatch body | .alwaysImplicit body
  | .alwaysEvent _ body | .alwaysFFR _ _ body _ | .initial body =>
      coreMemLocalDeclsStmt body
  | _ => []
end

def coreMemReactiveLaterWrites : List PProcess → List String
  | [] => []
  | p :: rest =>
      (if coreMemReactiveProc p then coreMemReactiveWrites p else []) ++
        coreMemReactiveLaterWrites rest

def coreMemFirstReadIn : List String → List String → Option String
  | [], _ => none
  | name :: rest, targets =>
      if targets.contains name then some name else coreMemFirstReadIn rest targets

def coreMemReactiveDependencyViol : List PProcess → Option String
  | [] => none
  | p :: rest =>
      if coreMemReactiveProc p then
        let targets := coreMemReactiveWrites p ++ coreMemReactiveLaterWrites rest
        match coreMemFirstReadIn (coreMemReactiveReadBeforeWrites p) targets with
        | some name => some name
        | none => coreMemReactiveDependencyViol rest
      else coreMemReactiveDependencyViol rest

def coreMemAssignReactiveChainViolAt (all : List PProcess) : List PProcess → Option String
  | [] => none
  | p :: rest =>
      match p with
      | .assign target value =>
          let reactiveWrites := all.flatMap fun q =>
            if coreMemReactiveProc q then coreMemReactiveWrites q else []
          let readNames := coreMemSignalNames value
          if readNames.any (fun name => reactiveWrites.contains name) then
            let downstream := all.any fun q =>
              coreMemSeparateReactiveProc q &&
                (coreMemReactiveReads q).any (fun name => name == target)
            if downstream then some target else coreMemAssignReactiveChainViolAt all rest
          else coreMemAssignReactiveChainViolAt all rest
      | .assignL target value =>
          let targetName := target.name
          let reactiveWrites := all.flatMap fun q =>
            if coreMemReactiveProc q then coreMemReactiveWrites q else []
          let readNames := coreMemSignalNames value
          if readNames.any (fun name => reactiveWrites.contains name) then
            let downstream := all.any fun q =>
              coreMemSeparateReactiveProc q &&
                (coreMemReactiveReads q).any (fun name => name == targetName)
            if downstream then some targetName else coreMemAssignReactiveChainViolAt all rest
          else coreMemAssignReactiveChainViolAt all rest
      | _ => coreMemAssignReactiveChainViolAt all rest

def coreMemAssignReactiveChainViol (processes : List PProcess) : Option String :=
  coreMemAssignReactiveChainViolAt processes processes

def coreMemCombDependencyViol (d : PDesign) (generated : List PProcess) :
    Option (String × String) :=
  let processes := d.processes ++ generated
  match coreMemReactiveDependencyViol processes with
  | none =>
      match coreMemAssignReactiveChainViol processes with
      | none => none
      | some name =>
          some ("Comb:dependency-order",
            s!"9.2.2.2/9.4.2.2/10.3: reactive output reaches continuous assignment '{name}' and a downstream reactive process; canonical E settles assignments before reactive activation and has no fixed-point scheduler")
  | some name =>
      some ("Comb:dependency-order",
        s!"9.2.2.2/9.4.2.2: reactive process reads '{name}' from itself or a later reactive process; canonical E has no fixed-point scheduler")


def PDesign.instantiateCoreMemFrom (envI : IEnv) (d : PDesign) (args : List Int)
    (iterFuel : Nat := 4096) : Res CoreMemDesign := do
  if args.length != d.params.length then
    .unsupported s!"parameter arity: got {args.length}, want {d.params.length}"
  else
    -- Constant functions are evaluated while binding parameter and localparam
    -- defaults.  Carry the parser-retained declarations into that scope
    -- before the first bind; attaching them only after `bindLocals` makes a
    -- module-local call look like an unsupported `CallExpression` even though
    -- its source-shaped pure function is admitted by the constant tier.
    let envI := { envI with functions := d.functions }
    let envP ← bindPackageEnums envI d.enums
    let envP ← bindPackageParams envP d.packageParams
    let env0 ← bindParamsRes envP d.params args
    let env1 ← bindLocals env0 d.localParams
    let env2 ← bindEnums env1 d.enums
    let pws ← typedParamWidthsE env2
      (d.params.map (fun p => (p.name, p.type?))
        ++ d.localParams.map (fun lp => (lp.name, lp.type?)))
    let env2 := { env2 with pwidths := pws }
    let env2 := { env2 with dims := dimTable env2 d.decls }
    let env2 := { env2 with functions := d.functions }
    let (generatedDecls, _) ← coreMemGeneratedDeclsList env2 iterFuel {} d.generates
    let localDecls := d.processes.flatMap coreMemLocalDeclsProc
    let sourceNames := (d.decls ++ generatedDecls ++ localDecls).map (·.name)
    let metadataForSource := d.netMetadata.filter (fun md => !md.generated)
    let sourceDecls := d.decls ++ generatedDecls ++ localDecls ++ coreMemMetadataDecls metadataForSource
    if !coreMemDeclNamesUnique sourceDecls then
      .unsupported "UnpackedDecl:generate-scope: active generate declarations contain duplicate names"
    else
      let env2 := { env2 with dims := dimTable env2 (d.decls ++ generatedDecls) }
      let (generatedRaw, _) ← coreMemExpandList env2 iterFuel {} d.generates
      let allForNet := d.processes ++ generatedRaw
      let generated := coreMemDropGeneratedNetMarkers d generatedRaw
      let generatedMetadataOk := d.netMetadata.all (fun md =>
        !md.generated || !sourceNames.contains md.name ||
          coreMemNetMetadataAllowed md || coreMemNetDriverAllowed md allForNet)
      if !generatedMetadataOk then
        .unsupported "NetSymbol:net-z:generate: generated net metadata does not prove a supported §6.6 net shape"
      else match coreMemEventSourceMultiWriteViol d generated with
      | some (kind, msg) => .unsupported s!"{kind}: {msg}"
      | none =>
          match coreMemEdgeBlockingReadRaceViol d generated with
          | some (kind, msg) => .unsupported s!"{kind}: {msg}"
          | none => match coreMemTimeZeroEventSourceViol d generated with
          | some (kind, msg) => .unsupported s!"{kind}: {msg}"
          | none =>
            let allProcesses := d.processes ++ generated
            if coreMemHasEdgeProc allProcesses && !coreMemPAssignMemoryTopoB allProcesses then
            .unsupported "Comb:memory-topology: 10.3/4.5: continuous assignment reads a memory cell driven by itself or a later assignment; canonical E requires topological source order"
            else match coreMemAssignReactiveChainViol (d.processes ++ generated) with
          | some name =>
              .unsupported s!"Comb:dependency-order: 9.2.2.2/9.4.2.2/10.3: reactive output reaches continuous assignment '{name}' and a downstream reactive process; canonical E settles assignments before reactive activation and has no fixed-point scheduler"
          | none =>
            match coreMemClockResetViol d generated with
            | some (kind, msg) => .unsupported s!"{kind}: {msg}"
            | none =>
              match coreMemFirstUnsupportedOther d allForNet d.others with
          | some (kind, text) =>
              .unsupported s!"E memory route does not yet admit module member '{kind}' ({text})"
          | none =>
              let decls0 ← buildScalarDecls1 env2 (d.decls ++ generatedDecls ++ localDecls)
              let declInitializers ← coreMemDeclInitializers env2
                (d.decls ++ generatedDecls ++ localDecls)
              let decls := decls0 ++ (coreMemNetDecls d allForNet).filter
                (fun dc => !sourceNames.contains dc.name)
              let elementDecls := sourceDecls.filter (fun pd => pd.aggregate?.isNone)
              let elems ← buildElems env2 elementDecls
              let envP := { env2 with widths := decls.map (fun dc => (dc.name, dc.width)) }
              let memories ← buildMemDecls1 envP (d.decls ++ generatedDecls) 0
              let aggregates ← buildAggDecls1 envP (d.decls ++ generatedDecls) 0
              if memories.isEmpty && (d.decls ++ generatedDecls).any (fun pd => !pd.unpackedDims.isEmpty) then
                .unsupported "UnpackedDecl:memory: no one-rank unpacked declaration was admitted"
              else
                let scalar : Elab :=
                  { name := d.name, decls := decls.toArray, procs := #[] }
                let scalarEdge : Elab1 :=
                  { decls := decls.toArray, procs := #[], name := d.name }
                let processes := (d.processes.map (CoreMemProc.ofPProcessAt envP)) ++
                  (d.primitives.map CoreMemProc.ofPPrimitive) ++
                  (generated.map (CoreMemProc.ofPProcessAt envP))
                let resolvedNets := coreMemResolvedNetNames d allForNet
                let result : CoreMemDesign :=
                    { name := d.name, env := envP, elems, scalar := scalar, scalarEdge := scalarEdge,
                      memories := memories.toArray, aggregates := aggregates.toArray,
                      processes := processes.toArray,
                      readmemh := d.readmemh, resolvedNets := resolvedNets,
                      declInitializers := declInitializers }
                .ok { result with compiledAssigns := result.compileAssigns }

/-! ## Expressions -/

mutual

/-- Whether an expression contains a parser-native aggregate member read.
This is named separately from `hasFunctionCall`: the clocked and comb scalar
profiles refuse aggregate storage because their theorem state has no aggregate
store, even though the legacy function-free gate also classifies it as outside
its fragment. -/
def LeanModels.Sv.PExpr.hasAggregateMember : PExpr → Bool
  | .aggregateMember .. | .packageAggElem .. => true
  | .unary _ a | .resize _ a | .signedResize _ a | .squash2 _ a
  | .sysCall _ a | .reduce _ a | .cast _ a => LeanModels.Sv.PExpr.hasAggregateMember a
  | .binary _ a b => LeanModels.Sv.PExpr.hasAggregateMember a ||
      LeanModels.Sv.PExpr.hasAggregateMember b
  | .ternary c a b => LeanModels.Sv.PExpr.hasAggregateMember c ||
      LeanModels.Sv.PExpr.hasAggregateMember a || LeanModels.Sv.PExpr.hasAggregateMember b
  | .concat xs | .functionCall _ xs => PExpr.hasAggregateMemberList xs
  | .bitSel a b | .repl a b => LeanModels.Sv.PExpr.hasAggregateMember a ||
      LeanModels.Sv.PExpr.hasAggregateMember b
  | .partSel a b c => LeanModels.Sv.PExpr.hasAggregateMember a ||
      LeanModels.Sv.PExpr.hasAggregateMember b || LeanModels.Sv.PExpr.hasAggregateMember c
  | .arrayElem _ indices => PExpr.hasAggregateMemberList indices
  | .arrayPart _ indices _ a b => PExpr.hasAggregateMemberList indices ||
      LeanModels.Sv.PExpr.hasAggregateMember a || LeanModels.Sv.PExpr.hasAggregateMember b
  | .lit _ | .ident _ | .paramRef .. | .genvarRef _ | .enumRef .. | .int _
  | .typeBits .. | .fill _ | .unsupported .. => false

def LeanModels.Sv.PExpr.hasAggregateMemberList : List PExpr → Bool
  | [] => false
  | x :: xs => LeanModels.Sv.PExpr.hasAggregateMember x ||
      LeanModels.Sv.PExpr.hasAggregateMemberList xs

def LeanModels.Sv.PExpr.hasMemoryRead : PExpr → Bool
  | .arrayElem .. | .arrayPart .. => true
  | .unary _ a | .resize _ a | .signedResize _ a | .squash2 _ a
  | .sysCall _ a | .reduce _ a | .cast _ a => LeanModels.Sv.PExpr.hasMemoryRead a
  | .binary _ a b => LeanModels.Sv.PExpr.hasMemoryRead a || LeanModels.Sv.PExpr.hasMemoryRead b
  | .ternary c a b => LeanModels.Sv.PExpr.hasMemoryRead c ||
      LeanModels.Sv.PExpr.hasMemoryRead a || LeanModels.Sv.PExpr.hasMemoryRead b
  | .concat xs => PExpr.hasMemoryReadList xs
  | .functionCall _ xs => PExpr.hasMemoryReadList xs
  | .bitSel a b | .repl a b => LeanModels.Sv.PExpr.hasMemoryRead a ||
      LeanModels.Sv.PExpr.hasMemoryRead b
  | .partSel a b c => LeanModels.Sv.PExpr.hasMemoryRead a ||
      LeanModels.Sv.PExpr.hasMemoryRead b || LeanModels.Sv.PExpr.hasMemoryRead c
  | .aggregateMember .. | .packageAggElem .. => true
  | .lit _ | .ident _ | .paramRef .. | .genvarRef _ | .enumRef .. | .int _
  | .typeBits .. | .fill _ | .unsupported .. => false

def LeanModels.Sv.PExpr.hasMemoryReadList : List PExpr → Bool
  | [] => false
  | x :: xs => LeanModels.Sv.PExpr.hasMemoryRead x ||
      LeanModels.Sv.PExpr.hasMemoryReadList xs

def LeanModels.Sv.PExpr.hasFunctionCall : PExpr → Bool
  | .functionCall _ _ => true
  | .sysCall _ _ => true
  | .unary _ a | .resize _ a | .signedResize _ a | .squash2 _ a
  | .reduce _ a | .cast _ a => LeanModels.Sv.PExpr.hasFunctionCall a
  | .binary _ a b => LeanModels.Sv.PExpr.hasFunctionCall a ||
      LeanModels.Sv.PExpr.hasFunctionCall b
  | .ternary c a b => LeanModels.Sv.PExpr.hasFunctionCall c ||
      LeanModels.Sv.PExpr.hasFunctionCall a || LeanModels.Sv.PExpr.hasFunctionCall b
  | .concat xs => PExpr.hasFunctionCallList xs
  | .bitSel a b | .repl a b => LeanModels.Sv.PExpr.hasFunctionCall a ||
      LeanModels.Sv.PExpr.hasFunctionCall b
  | .partSel a b c => LeanModels.Sv.PExpr.hasFunctionCall a ||
      LeanModels.Sv.PExpr.hasFunctionCall b || LeanModels.Sv.PExpr.hasFunctionCall c
  | .arrayElem _ indices => PExpr.hasFunctionCallList indices
  | .arrayPart _ indices _ a b => PExpr.hasFunctionCallList indices ||
      LeanModels.Sv.PExpr.hasFunctionCall a || LeanModels.Sv.PExpr.hasFunctionCall b
  -- The scalar/memory cycle refinement theorem does not carry the aggregate
  -- store.  Classify this source-shaped read as outside that theorem's
  -- function-free fragment, while canonical E evaluates it through
  -- `evalAggregateMember` above.
  | .aggregateMember .. | .packageAggElem .. => true
  | .lit _ | .ident _ | .paramRef .. | .genvarRef _ | .enumRef .. | .int _
  | .typeBits .. | .fill _ | .unsupported .. => false

def LeanModels.Sv.PExpr.hasFunctionCallList : List PExpr → Bool
  | [] => false
  | x :: xs => LeanModels.Sv.PExpr.hasFunctionCall x ||
      LeanModels.Sv.PExpr.hasFunctionCallList xs

end

/-! ## Raw sensitivity for retained implicit processes

Plain `always @*` is sensitive to every value read by its body (§9.4.2.2.2),
including the selected cell and index of a source-shaped memory read.  These
walkers retain the parser expressions; they do not lower a body or collapse a
memory into scalar cells. -/

mutual

def _root_.LeanModels.Sv.PExpr.hasGenvarRef : PExpr → Bool
  | .genvarRef _ => true
  | .unary _ a | .resize _ a | .signedResize _ a | .squash2 _ a
  | .sysCall _ a | .reduce _ a | .cast _ a => a.hasGenvarRef
  | .binary _ a b | .bitSel a b | .repl a b => a.hasGenvarRef || b.hasGenvarRef
  | .partSel a b c | .ternary a b c => a.hasGenvarRef || b.hasGenvarRef || c.hasGenvarRef
  | .concat xs | .functionCall _ xs => PExpr.hasGenvarRefList xs
  | .arrayElem _ xs => PExpr.hasGenvarRefList xs
  | .arrayPart _ xs _ a b => PExpr.hasGenvarRefList xs || a.hasGenvarRef || b.hasGenvarRef
  | .aggregateMember _ path => PExpr.hasGenvarRefPath path
  | .packageAggElem _ _ index => index.hasGenvarRef
  | _ => false

def _root_.LeanModels.Sv.PExpr.hasGenvarRefList : List PExpr → Bool
  | [] => false
  | x :: xs => x.hasGenvarRef || PExpr.hasGenvarRefList xs

def _root_.LeanModels.Sv.PExpr.hasGenvarRefPath : List (Option String × Option PExpr) → Bool
  | [] => false
  | (_, none) :: rest => PExpr.hasGenvarRefPath rest
  | (_, some e) :: rest => e.hasGenvarRef || PExpr.hasGenvarRefPath rest

end

mutual

def coreMemReadExprs : PExpr → List PExpr
  | e@(.ident _) => [e]
  | e@(.arrayElem _ indices) => e :: coreMemReadExprsList indices
  | e@(.arrayPart _ indices _ a b) =>
      e :: (coreMemReadExprsList indices ++ coreMemReadExprs a ++ coreMemReadExprs b)
  | e@(.aggregateMember _ _) => [e]
  | e@(.packageAggElem _ _ _) => [e]
  | .unary _ a | .resize _ a | .signedResize _ a | .squash2 _ a
  | .sysCall _ a | .reduce _ a | .cast _ a => coreMemReadExprs a
  | .binary _ a b | .bitSel a b | .repl a b =>
      coreMemReadExprs a ++ coreMemReadExprs b
  | .partSel a b c | .ternary a b c =>
      coreMemReadExprs a ++ coreMemReadExprs b ++ coreMemReadExprs c
  | .concat xs | .functionCall _ xs => coreMemReadExprsList xs
  | .lit _ | .fill _ | .paramRef .. | .genvarRef _ | .enumRef .. | .int _
  | .typeBits .. | .unsupported .. => []

def coreMemReadExprsList : List PExpr → List PExpr
  | [] => []
  | e :: rest => coreMemReadExprs e ++ coreMemReadExprsList rest

def coreMemLhsReadExprs : PLhs → List PExpr
  | .ident _ => []
  | .bitSel _ i => coreMemReadExprs i
  | .partSel _ a b => coreMemReadExprs a ++ coreMemReadExprs b
  | .concat xs => coreMemLhsReadExprsList xs
  | .arrayElem _ indices => coreMemReadExprsList indices
  | .arrayPart _ indices _ a b =>
      coreMemReadExprsList indices ++ coreMemReadExprs a ++ coreMemReadExprs b
  | .aggregateMember _ path =>
      (path.filterMap (fun step => step.2)).flatMap coreMemReadExprs

def coreMemLhsReadExprsList : List PLhs → List PExpr
  | [] => []
  | lhs :: rest => coreMemLhsReadExprs lhs ++ coreMemLhsReadExprsList rest

def coreMemStmtReadExprs : PStmt → List PExpr
  | .localDecl _ _ init => init.toList.flatMap coreMemReadExprs
  | .automaticDecl _ _ init => init.toList.flatMap coreMemReadExprs
  | .blockingAssign _ value | .nbaAssign _ value => coreMemReadExprs value
  | .blockingAssignL target value | .nbaAssignL target value =>
      coreMemLhsReadExprs target ++ coreMemReadExprs value
  | .ifStmt cond yes no =>
      coreMemReadExprs cond ++ coreMemStmtReadExprs yes ++ coreMemStmtReadExprsOpt no
  | .block body => coreMemStmtReadExprsList body
  | .forLoop _ init condition step body =>
      coreMemReadExprs init ++ coreMemReadExprs condition ++ coreMemReadExprs step ++
        coreMemStmtReadExprs body
  | .caseStmt subject items default? _ _ =>
      coreMemReadExprs subject ++ coreMemCaseReadExprs items ++
        coreMemStmtReadExprsOpt default?
  | .unsupported .. => []


def coreMemStmtReadExprsOpt : Option PStmt → List PExpr
  | none => []
  | some body => coreMemStmtReadExprs body

def coreMemStmtReadExprsList : List PStmt → List PExpr
  | [] => []
  | stmt :: rest => coreMemStmtReadExprs stmt ++ coreMemStmtReadExprsList rest

def coreMemCaseReadExprs : List (List PExpr × PStmt) → List PExpr
  | [] => []
  | (patterns, body) :: rest =>
      coreMemReadExprsList patterns ++ coreMemStmtReadExprs body ++
        coreMemCaseReadExprs rest

end

mutual

partial def coreMemAutomaticNames : PStmt → List String
  | .automaticDecl name _ _ => [name]
  | .localDecl _ _ _ | .blockingAssign _ _ | .nbaAssign _ _ | .unsupported .. => []
  | .blockingAssignL _ _ | .nbaAssignL _ _ => []
  | .ifStmt _ yes none => coreMemAutomaticNames yes
  | .ifStmt _ yes (some no) => coreMemAutomaticNames yes ++ coreMemAutomaticNames no
  | .block body => coreMemAutomaticNamesList body
  | .forLoop _ _ _ _ body => coreMemAutomaticNames body
  | .caseStmt _ items default? _ _ =>
      coreMemAutomaticNamesCase items ++ default?.toList.flatMap coreMemAutomaticNames

partial def coreMemAutomaticNamesList : List PStmt → List String
  | [] => []
  | stmt :: rest => coreMemAutomaticNames stmt ++ coreMemAutomaticNamesList rest

partial def coreMemAutomaticNamesCase : List (List PExpr × PStmt) → List String
  | [] => []
  | (_, body) :: rest => coreMemAutomaticNames body ++ coreMemAutomaticNamesCase rest

end

def coreMemExternalReadExprs (body : PStmt) : List PExpr :=
  let locals := coreMemAutomaticNames body
  (coreMemStmtReadExprs body).filter fun expr =>
    match expr with
    | .ident name => !locals.contains name
    | _ => true

/-! IEEE 1800-2023 §9.2.2.2.1 removes variables written by an
`always_comb` body from that block's implicit sensitivity list.  Keep this
separate from the raw `always @*` read set above: §9.4.2.2 includes the
variables read by an implicit event control, while `always_comb` deliberately
does not re-arm on its own writes. -/
def coreMemCombExternalReadExprs (body : PStmt) : List PExpr :=
  let locals := coreMemAutomaticNames body
  let writes := coreMemStmtWrites body
  (coreMemStmtReadExprs body).filter fun expr =>
    match expr with
    | .ident name => !locals.contains name && !writes.contains name
    | _ => true


/-! The ordinary E entry is defined after the source-shaped sensitivity
walkers so its derived cache is built once at instantiation, never in a cycle.
The source nodes remain in `CoreMemProc`; this is an evaluator cache only. -/

def CoreMemDesign.compileCombReads (E : CoreMemDesign) :
    Array (Option (List Expr2)) :=
  E.processes.map fun p =>
    match p with
    | .comb body =>
        let reads := coreMemCombExternalReadExprs body
        if reads.all (fun e => !LeanModels.Sv.PExpr.hasMemoryRead e &&
            !LeanModels.Sv.PExpr.hasFunctionCall e) then
          some (reads.map (instExpr2 E.env E.elems none))
        else none
    | _ => none

def CoreMemDesign.compileImplicitReads (E : CoreMemDesign) :
    Array (Option (List Expr2)) :=
  E.processes.map fun p =>
    match p with
    | .implicit body =>
        let reads := coreMemExternalReadExprs body
        if reads.all (fun e => !LeanModels.Sv.PExpr.hasMemoryRead e &&
            !LeanModels.Sv.PExpr.hasFunctionCall e) then
          some (reads.map (instExpr2 E.env E.elems none))
        else none
    | _ => none

def PDesign.instantiateCoreMem (d : PDesign) (args : List Int)
    (iterFuel : Nat := 4096) : Res CoreMemDesign := do
  let result ← PDesign.instantiateCoreMemFrom { int32 := true } d args iterFuel
  .ok { result with
    compiledCombReads := result.compileCombReads
    compiledImplicitReads := result.compileImplicitReads }

/-! The ordinary E entry.  Parameterized unpacked declarations are canonical
E storage, so callers must not silently fall back to the scalar `EDesign2`
view.  The old scalar-only elaboration remains available explicitly as
`instantiateE2Scalar`; this name is the user-facing route for both fixed and
parameter-sized one-rank memories (IEEE 1800-2023 §7.4.2). -/

def PDesign.instantiateE2 (d : PDesign) (args : List Int) (iterFuel : Nat := 4096) :
    Res CoreMemDesign :=
  PDesign.instantiateCoreMem d args iterFuel

def evalMemUnary (op : SymUnaryOp) (v : LVec) : Res LVec :=
  match op with
  | .m0 op => .ok (evalUnaryOp op v)
  | .plus => .ok (evalUnaryOp .pos v)
  | .inc | .dec => .unsupported
    "UnaryExpression:incdec: increment/decrement is only a procedural loop step"

def evalMemBin (op : SymBinOp) (a b : LVec) : Res LVec :=
  match op with
  | .m0 op => .ok (evalBinOp op a b)
  | .mul => .ok (evalBinOp .mul a b)
  | .div => .ok (evalBinOp .div a b)
  | .mod => .ok (evalBinOp .rem a b)
  | .pow => .ok (evalBinOp (.pow false false) a b)
  | .shl => .ok (evalBinOp (.shl false) a b)
  | .shr => .ok (evalBinOp (.shr false) a b)
  | .ashl => .ok (evalBinOp (.ashl false) a b)
  | .ashr => .ok (evalBinOp (.ashr false) a b)
  | .slt => .ok (evalBinOp .slt a b)
  | .sle => .ok (evalBinOp .sle a b)
  | .sgt => .ok (evalBinOp .sgt a b)
  | .sge => .ok (evalBinOp .sge a b)
  | .ceq => .ok (evalBinOp .caseEq a b)
  | .cne => .ok (evalBinOp .caseNe a b)
  | .land => .ok (evalBinOp .land a b)
  | .lor => .ok (evalBinOp .lor a b)

def CoreMemDesign.evalScalarLocals (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (ctx : Option Nat) (locals : SvState) (e : PExpr) : Res LVec :=
  let widths := if elems.isEmpty then E.elems else elems
  evalPure2 (locals ++ E.scalar.view st.scalar) (instExpr2 env widths ctx e)

def CoreMemDesign.evalScalar (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (ctx : Option Nat) (e : PExpr) : Res LVec :=
  E.evalScalarLocals env elems st ctx [] e

def CoreMemDesign.evalFunctionArgs (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (locals : SvState) : List PDecl → List PExpr → Res (List LVec)
  | [], [] => .ok []
  | formal :: formals, actual :: actuals => do
      let width ← match formal.type.width env with
        | .ok w => .ok w
        | .error msg => .unsupported s!"function formal '{formal.name}': {msg}"
      let value ← E.evalScalarLocals env elems st (some width) locals actual
      let value := if formal.isSigned then value.resizeSigned width else value.resizeU width
      let rest ← E.evalFunctionArgs env elems st locals formals actuals
      .ok (value :: rest)
  | _ :: _, [] | [], _ :: _ => .unsupported "CallExpression:user-function:arity"

/-! A source-shaped function call keeps the parser's `PExpr.functionCall`
node.  IEEE 1800-2023 §§13.4–13.5 define the automatic function's input
formal binding, expression evaluation, and return conversion; the evaluator
implements that direct call here rather than replacing the node with an
inlined expression.  Static functions and output/ref/inout formals remain
named refusals because their storage and side effects are outside this
source-shaped expression subset. -/
def CoreMemDesign.evalFunction (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (locals : SvState) (name : String) (args : List PExpr) : Res LVec :=
  match env.functions.find? (fun f => f.name == name) with
  | none => .unsupported s!"CallExpression:user-function: function '{name}' is not declared"
  | some f =>
      if !f.automatic then
        .unsupported s!"SubroutineSymbol:static: function '{name}' is not automatic"
      else if f.formals.any (fun formal => !formal.isInput) then
        .unsupported s!"SubroutineSymbol:formal: function '{name}' formals must be input-only"
      else
        match f.returnType.width env with
        | .error msg => .unsupported s!"SubroutineSymbol:return-type: {msg}"
        | .ok returnWidth => do
            let values ← E.evalFunctionArgs env elems st locals f.formals args
            let bindings := f.formals.zip values |>.map fun (formal, value) => (formal.name, value)
            let value ← E.evalScalarLocals env elems st (some returnWidth) bindings f.body
            .ok (if f.isSigned then value.resizeSigned returnWidth else value.resizeU returnWidth)

/-! `$test$plusargs` takes a source string pattern.  String literals are
    represented by the parser as known packed vectors, with the first source
    character in the most-significant byte. -/

def coreMemStringLiteral? : PExpr → Option String
  | .lit value =>
      if value.width == 0 || value.width % 8 != 0 || !value.allKnown then none
      else
        let bytes := value.width / 8
        some (String.ofList ((List.range bytes).reverse.map fun index =>
          Char.ofNat ((value.toNat / (2 ^ (8 * index))) % 256)))
  | _ => none

def CoreMemDesign.evalSysCall (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) (locals : SvState)
    (fn : SysFn) (arg : PExpr) : Res LVec :=
  match fn with
  | .testPlusargs =>
      match coreMemStringLiteral? arg with
      | some pattern =>
          .ok (LVec.ofLogic (if Plusargs.test E.plusargs pattern then .l1 else .l0))
      | none => .unsupported
          "SysCall:$test$plusargs: argument must be a known string literal"
  | _ => E.evalScalarLocals env elems st none locals (.sysCall fn arg)

mutual

def CoreMemDesign.evalIndexLocals (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (locals : SvState) (e : PExpr) : Res LVec :=
  match evalInt env e with
  | .ok i => .ok (LVec.ofInt 32 i)
  | .error _ => E.evalExprLocals env elems st none locals e

def CoreMemDesign.evalAggPath (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (locals : SvState) :
    List (Option String × Option PExpr) → Res AggPath
  | [] => .ok []
  | (some field, none) :: rest => do
      let tail ← E.evalAggPath env elems st locals rest
      .ok (.field field :: tail)
  | (none, some index) :: rest => do
      let iv ← E.evalIndexLocals env elems st locals index
      let some value := LVec.toInt? iv
        | .unsupported "MemberAccessExpression:aggregate: unknown index"
      let tail ← E.evalAggPath env elems st locals rest
      .ok (.index value :: tail)
  | _ :: _ => .unsupported "MemberAccessExpression:aggregate: malformed path"

def CoreMemDesign.evalAggregateMember (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) (locals : SvState)
    (base : String) (path : List (Option String × Option PExpr)) : Res LVec := do
  let some decl := E.aggregateDecl? base
    | .unsupported s!"MemberAccessExpression:aggregate: declaration '{base}' is not present"
  let steps ← E.evalAggPath env elems st locals path
  let some value := st.aggregates.read? decl.id steps
    | .unsupported s!"MemberAccessExpression:aggregate: path in '{base}' is invalid"
  .ok value.bits

def CoreMemDesign.evalExprLocals (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (ctx : Option Nat) (locals : SvState) : PExpr → Res LVec
  | e@(.arrayElem name [index]) => do
      match E.memDecl? name with
      | some md =>
          let idx ← E.evalIndexLocals env elems st locals index
          match st.memory.readIndexId md.shape.id index.signedCast idx with
          | some v => .ok v
          | none => .unsupported s!"ArraySel: memory identity for '{name}' is not present"
      | none => E.evalScalarLocals env elems st ctx locals e
  | e@(.arrayElem name _) =>
      if E.memDecl? name |>.isSome then
        .unsupported s!"ArraySel:rank: memory '{name}' is not a one-rank element select"
      else E.evalScalarLocals env elems st ctx locals e
  | e@(.arrayPart name _ _ _ _) =>
      match E.memDecl? name with
      | some _ =>
          .unsupported s!"ArraySel:part: memory '{name}' part select is outside this E slice"
      | none => E.evalScalarLocals env elems st ctx locals e
  | .aggregateMember base path => E.evalAggregateMember env elems st locals base path
  | e@(.bitSel base index) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then do
        let bv ← E.evalExprLocals env elems st none locals base
        let iv ← E.evalIndexLocals env elems st locals index
        let position? := if index.signedCast then iv.toInt?
          else iv.toNat?.map Int.ofNat
        match position? with
        | some position =>
            if 0 ≤ position && position < bv.width then
              .ok (bv.extract position.toNat 1)
            else .ok (LVec.xVec 1)
        | none => .ok (LVec.xVec 1)
      else E.evalScalarLocals env elems st ctx locals e
  | .functionCall name args => E.evalFunction env elems st locals name args
  | e@(.unary op a) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then do
        evalMemUnary op (← E.evalExprLocals env elems st ctx locals a)
      else E.evalScalarLocals env elems st ctx locals e
  | e@(.binary op a b) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then do
        evalMemBin op (← E.evalExprLocals env elems st ctx locals a)
          (← E.evalExprLocals env elems st ctx locals b)
      else E.evalScalarLocals env elems st ctx locals e
  | e@(.ternary c a b) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then
        do
          let cv ← E.evalExprLocals env elems st none locals c
          let tv ← E.evalExprLocals env elems st ctx locals a
          let fv ← E.evalExprLocals env elems st ctx locals b
          .ok (LVec.ternary cv tv fv)
      else E.evalScalarLocals env elems st ctx locals e
  | e@(.concat xs) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then do
        let vs ← E.evalMemExprListLocals env elems st locals xs
        .ok (LVec.concatMany vs.toArray)
      else E.evalScalarLocals env elems st ctx locals e
  | e@(.resize _ a) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then do
        let v ← E.evalExprLocals env elems st ctx locals a
        .ok (v.resizeU (ctx.getD v.width))
      else E.evalScalarLocals env elems st ctx locals e
  | e@(.signedResize _ a) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then do
        let v ← E.evalExprLocals env elems st ctx locals a
        .ok (v.resizeSigned (ctx.getD v.width))
      else E.evalScalarLocals env elems st ctx locals e
  | e@(.squash2 _ a) =>
      if LeanModels.Sv.PExpr.hasMemoryRead e then do
        return (← E.evalExprLocals env elems st ctx locals a).toTwoState
      else E.evalScalarLocals env elems st ctx locals e
  | e => E.evalScalarLocals env elems st ctx locals e

def CoreMemDesign.evalMemExprListLocals (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (locals : SvState) : List PExpr → Res (List LVec)
  | [] => .ok []
  | e :: es => do
      let v ← E.evalExprLocals env elems st none locals e
      let vs ← E.evalMemExprListLocals env elems st locals es
      .ok (v :: vs)

end

def CoreMemDesign.evalIndex (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (e : PExpr) : Res LVec :=
  E.evalIndexLocals env elems st [] e

def CoreMemDesign.evalExpr (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (ctx : Option Nat) (e : PExpr) : Res LVec :=
  E.evalExprLocals env elems st ctx [] e

mutual
def LeanModels.Sv.PExpr.hasTestPlusargs : PExpr → Bool
  | .sysCall .testPlusargs _ => true
  | .unary _ a | .resize _ a | .signedResize _ a | .squash2 _ a
  | .sysCall _ a | .reduce _ a | .cast _ a => LeanModels.Sv.PExpr.hasTestPlusargs a
  | .binary _ a b => LeanModels.Sv.PExpr.hasTestPlusargs a || LeanModels.Sv.PExpr.hasTestPlusargs b
  | .ternary c a b => LeanModels.Sv.PExpr.hasTestPlusargs c ||
      LeanModels.Sv.PExpr.hasTestPlusargs a || LeanModels.Sv.PExpr.hasTestPlusargs b
  | .concat xs => LeanModels.Sv.PExpr.hasTestPlusargsList xs
  | .bitSel a b | .repl a b => LeanModels.Sv.PExpr.hasTestPlusargs a ||
      LeanModels.Sv.PExpr.hasTestPlusargs b
  | .partSel a b c => LeanModels.Sv.PExpr.hasTestPlusargs a ||
      LeanModels.Sv.PExpr.hasTestPlusargs b || LeanModels.Sv.PExpr.hasTestPlusargs c
  | .arrayElem _ xs => LeanModels.Sv.PExpr.hasTestPlusargsList xs
  | .arrayPart _ xs _ a b => LeanModels.Sv.PExpr.hasTestPlusargsList xs ||
      LeanModels.Sv.PExpr.hasTestPlusargs a || LeanModels.Sv.PExpr.hasTestPlusargs b
  | .functionCall _ xs => LeanModels.Sv.PExpr.hasTestPlusargsList xs
  | _ => false

def LeanModels.Sv.PExpr.hasTestPlusargsList : List PExpr → Bool
  | [] => false
  | x :: xs => LeanModels.Sv.PExpr.hasTestPlusargs x ||
      LeanModels.Sv.PExpr.hasTestPlusargsList xs
end

def CoreMemDesign.evalRuntimeExpr (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) (ctx : Option Nat)
    (e : PExpr) : Res LVec :=
  match e with
  | .sysCall fn arg => E.evalSysCall env elems st [] fn arg
  | .ternary c a b => do
      let cv ← E.evalRuntimeExpr env elems st none c
      let tv ← if LeanModels.Sv.PExpr.hasTestPlusargs a then E.evalRuntimeExpr env elems st ctx a
        else E.evalExprLocals env elems st ctx [] a
      let fv ← if LeanModels.Sv.PExpr.hasTestPlusargs b then E.evalRuntimeExpr env elems st ctx b
        else E.evalExprLocals env elems st ctx [] b
      .ok (LVec.ternary cv tv fv)
  | _ => E.evalExprLocals env elems st ctx [] e


/-! A continuous scalar assignment has no local bindings.  Once the source
expression has no native-memory read, its `Expr2` lowering is independent of
the state and can be reused from `CoreMemDesign.compiledAssigns`; a memory
read must stay on `evalExpr`, whose source-shaped evaluator threads
`MemState`. -/
def CoreMemDesign.evalScalarAssignAtView (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) (view : SvState)
    (ctx : Option Nat) (index : Nat) (value : PExpr) : Res LVec :=
  if LeanModels.Sv.PExpr.hasTestPlusargs value &&
      LeanModels.Sv.PExpr.hasFunctionCall value then
    -- Calls, including `$test$plusargs`, depend on the explicit runtime
    -- environment carried by `CoreMemDesign`.  Keep the parser-shaped
    -- expression on the source evaluator instead of asking `Expr2` to
    -- manufacture a declared-signal value for an external query.
    E.evalRuntimeExpr env elems st ctx value
  else if LeanModels.Sv.PExpr.hasMemoryRead value ||
            LeanModels.Sv.PExpr.hasAggregateMember value then
    E.evalExpr env elems st ctx value
  else
    match E.compiledAssigns[index]? with
    | some (some compiled) => evalPure2 view compiled
    | _ => E.evalExpr env elems st ctx value

def CoreMemDesign.evalScalarAssignAt (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) (ctx : Option Nat)
    (index : Nat) (value : PExpr) : Res LVec :=
  E.evalScalarAssignAtView env elems st (E.scalar.view st.scalar) ctx index value

def evalMemExprList (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) : List PExpr → Res (List LVec)
  | [] => .ok []
  | e :: es => do
      let v ← E.evalExpr env elems st none e
      let vs ← evalMemExprList E env elems st es
      .ok (v :: vs)

/-! ## Source-shaped case selection

Case selection stays on the retained `PStmt.caseStmt` node.  Patterns are
evaluated in the current state, compared with the parser's IEEE case matcher,
and the first matching arm is returned without rewriting the arm into an
`if` chain.  Qualified-case claims inspect every arm before the selected arm
runs; `casez`/`casex` use the same parser-native wildcard matcher. -/

def coreMemCaseHits (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (subject : LVec) (mode : CaseMode) :
    List (List PExpr × PStmt) → Res Nat
  | [] => .ok 0
  | (patterns, _) :: rest => do
      let values ← evalMemExprList E env elems st patterns
      let n ← coreMemCaseHits E env elems st subject mode rest
      .ok (if values.any (fun value => caseHit mode subject value) then n + 1 else n)

def coreMemSelectCase (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (subject : LVec) (mode : CaseMode) :
    List (List PExpr × PStmt) → Option PStmt → Res (Option PStmt)
  | [], default? => .ok default?
  | (patterns, body) :: rest, default? => do
      let values ← evalMemExprList E env elems st patterns
      if values.any (fun value => caseHit mode subject value) then
        .ok (some body)
      else
        coreMemSelectCase E env elems st subject mode rest default?

/-! ## Source-shaped edge bodies -/

/- An edge activation carries both the state changed immediately by blocking
assignments and the updates deferred to the NBA region.  Keeping the state in
the result is what makes source order observable: a later statement samples a
value written by an earlier blocking assignment, while an NBA still samples
the state at its issue site. -/
structure CoreMemExecResult where
  state : CoreMemState
  scalarQ : NbaQueue2
  memoryQ : MemNbaQueue
  /-- Automatic procedural locals live only for this source activation. -/
  locals : SvState := []

abbrev CoreMemExec := Res CoreMemExecResult

abbrev CoreMemQueue := NbaQueue2 × MemNbaQueue

def CoreMemDesign.scalarTarget (E : CoreMemDesign) (name : String) : Option Nat :=
  E.scalarWidth? name

/-! A parser-native select target can name either a retained unpacked memory or
 a packed scalar declaration.  The former stays on `MemState`; the latter is
 lowered to the existing `Lhs2` window resolver used by E's scalar semantics.
This distinction is required for source-shaped edge bodies such as
`decoded_rs1[regindex_bits-1] <= 1` beside `cpuregs[latched_rd] <= ...`.
The source `PLhs` node remains the authority; `instLhs2` is only the existing
window interpretation of that node (IEEE 1800-2023 §11.5.1). -/
def CoreMemDesign.scalarLhs2 (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (target : PLhs) : Res (Lhs2 × Nat) :=
  match instLhs2 env elems target with
  | .ok result => .ok result
  | .error msg => .unsupported s!"11.5.1: scalar select target: {msg}"

def scalarNbaWindows (value : LVec) : List (String × Nat × Nat) → NbaQueue2
  | windows =>
      let total := windows.foldl (fun n (_, _, width) => n + width) 0
      let replacement := value.resizeU total
      let rec go (remaining : List (String × Nat × Nat))
          (remainingWidth : Nat) : NbaQueue2 :=
        match remaining with
        | [] => []
        | (name, lo, width) :: rest =>
            let nextWidth := remainingWidth - width
            (name, lo, replacement.extract nextWidth width) ::
              go rest nextWidth
      go windows total

def CoreMemDesign.writeScalarLhs2 (E : CoreMemDesign) (st : CoreMemState)
    (lhs : Lhs2) (value : LVec) : Res CoreMemState :=
  let view := E.scalar.view st.scalar
  match lhs with
  | .concat _ => do
      let windows ← resolveConcatLhs2 4096 view lhs
      let view' ← writeConcatLhs2 view value windows
      .ok (E.compactScalar st view')
  | _ => do
      let (name, window) ← resolveLhs2 4096 view lhs
      match window with
      | none => .ok st
      | some (lo, width) =>
          match E.scalar.resolve name with
          | none => .unsupported s!"11.5.1: scalar select target '{name}' is undeclared"
          | some x =>
              let old := st.scalar x
              .ok (E.setScalarState st name
                (old.bits.insertAt lo (value.resizeU width)))

def CoreMemDesign.execScalarTarget (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) (target : PLhs)
    (value : PExpr) : Res CoreMemState := do
  let (lhs, width) ← E.scalarLhs2 env elems target
  let v ← E.evalExpr env elems st (some width) value
  E.writeScalarLhs2 st lhs v

def CoreMemDesign.issueScalarTarget (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) (target : PLhs)
    (value : LVec) : Res CoreMemQueue := do
  let (lhs, _) ← E.scalarLhs2 env elems target
  let view := E.scalar.view st.scalar
  let windows ← resolveConcatLhs2 4096 view lhs
  .ok (scalarNbaWindows value windows, [])

def CoreMemDesign.issueTarget (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (target : PLhs) (value : LVec) : Res CoreMemQueue :=
  match target with
  | .ident name =>
      match E.scalarTarget name with
      | some _ => .ok ([(name, 0, value)], [])
      | none => .unsupported s!"11.5.1: scalar NBA target '{name}' is undeclared"
  | .arrayElem name indices =>
      match E.memDecl? name with
      | none => E.issueScalarTarget env elems st (.arrayElem name indices) value
      | some md =>
          match indices with
          | [index] =>
              let idx := E.evalIndex env elems st index
              match idx with
              | .timeout => .timeout
              | .unsupported m => .unsupported m
              | .ok iv =>
                  match st.memory.issueNba md.shape.id index.signedCast iv value with
                  | .missing => .unsupported s!"11.5.1: memory identity for '{name}' is not present"
                  | .noOp => .ok ([], [])
                  | .queued u => .ok ([], [u])
          | _ => .unsupported s!"11.5.1: memory NBA target '{name}' is not one-rank"
  | target => E.issueScalarTarget env elems st target value

def CoreMemDesign.writeMemoryAssign (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) (target : PLhs)
    (md : CoreMemDecl) (value : LVec) : Res CoreMemState :=
  match target with
  | .arrayElem _ [(.int k)] =>
      match st.memory.lookupId md.shape.id with
      | some block =>
          let converted := md.shape.convert value
          if block.read k == converted then .ok st
          else
            match LeanModels.Sv.MemState.writeTarget env md.source target value st.memory with
            | .error msg => .unsupported msg
            | .ok none => .unsupported "10.3: continuous target is not one-rank"
            | .ok (some memory) => .ok { st with memory }
      | none => .unsupported s!"10.3: memory identity for '{md.source.name}' is not present"
  | _ =>
      match LeanModels.Sv.MemState.writeTarget env md.source target value st.memory with
      | .error msg => .unsupported msg
      | .ok none => .unsupported "10.3: continuous target is not one-rank"
      | .ok (some memory) => .ok { st with memory }

def CoreMemDesign.writeScalarBitAssign (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) (name : String)
    (index : PExpr) (value : PExpr) : Res CoreMemState := do
  let width ← match E.scalarWidth? name with
    | some w => .ok w
    | none => .unsupported s!"10.3: scalar target '{name}' is undeclared"
  let iv ← E.evalIndex env elems st index
  let vv ← E.evalExpr env elems st (some 1) value
  let current ← match E.scalar.resolve name with
    | some x => .ok (st.scalar x)
    | none => .unsupported s!"10.3: scalar target '{name}' is undeclared"
  let position? := if index.signedCast then iv.toInt?
    else iv.toNat?.map Int.ofNat
  match position? with
  | some position =>
      if 0 ≤ position && position < width then
        .ok (E.setScalarState st name (current.bits.insertAt position.toNat vv))
      else .ok st
  | none => .ok st

/-! A packed part-select target is the source-shaped port-connection form
used by a parameterized child (`y[W/2-1:0]`).  Bounds are constants after
the parent point is instantiated; preserve the target window with the same
LSB-first `LVec.insertAt` primitive used by scalar bit writes. -/
def CoreMemDesign.writeScalarPartAssign (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) (name : String)
    (msb lsb : PExpr) (value : LVec) : Res CoreMemState := do
  let width ← match E.scalarWidth? name with
    | some w => .ok w
    | none => .unsupported s!"10.3: scalar target '{name}' is undeclared"
  let hi ← E.evalIndex env elems st msb
  let lo ← E.evalIndex env elems st lsb
  let some hi := hi.toNat? | .unsupported "10.3: packed part-select bound is unknown"
  let some lo := lo.toNat? | .unsupported "10.3: packed part-select bound is unknown"
  if hi < lo then
    .unsupported "10.3: packed part-select has descending runtime bounds"
  else if hi >= width then
    .unsupported "10.3: packed part-select upper bound is outside the scalar target"
  else
    match E.scalar.resolve name with
    | some x =>
        let old := st.scalar x
        let w := hi - lo + 1
        .ok (E.setScalarState st name (old.bits.insertAt lo (value.resizeU w)))
    | none => .unsupported s!"10.3: scalar target '{name}' is undeclared"

/-! A whole unpacked-array port connection remains a source-shaped array
assignment.  Its runtime meaning is the ordinary continuous assignment of
each element to the child declaration; `MemState.copyId` performs that copy
without expanding the declaration into cells. -/
def CoreMemDesign.copyMemoryAssign (E : CoreMemDesign) (st : CoreMemState)
    (target source : String) : Res CoreMemState :=
  match E.memDecl? target, E.memDecl? source with
  | some dst, some src =>
      match st.memory.copyId src.shape.id dst.shape.id with
      | some memory => .ok { st with memory }
      | none => .unsupported
          s!"23.3.3: unpacked port connection '{source}' to '{target}' has incompatible bounds"
  | none, _ => .unsupported s!"23.3.3: unpacked port target '{target}' is undeclared"
  | _, none => .unsupported s!"23.3.3: unpacked port actual '{source}' is undeclared"

def CoreMemExec.fromQueue (st : CoreMemState) : Res CoreMemQueue → CoreMemExec
  | .ok (scalarQ, memoryQ) => .ok { state := st, scalarQ, memoryQ }
  | .timeout => .timeout
  | .unsupported msg => .unsupported msg

def CoreMemExec.withLocals (locals : SvState) : CoreMemExec → CoreMemExec
  | .ok result => .ok { result with locals }
  | .timeout => .timeout
  | .unsupported msg => .unsupported msg

def CoreMemExec.append (a b : CoreMemExecResult) : CoreMemExecResult :=
  { state := b.state, scalarQ := a.scalarQ ++ b.scalarQ, memoryQ := a.memoryQ ++ b.memoryQ,
    locals := b.locals }

def setAutomaticLocal (locals : SvState) (name : String) (value : LVec) : SvState :=
  SvState.set locals name value

def CoreMemDesign.execAutomaticDecl (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) (locals : SvState)
    (name : String) (width : Nat) (init : Option PExpr) : Res SvState := do
  let value ← match init with
    | none => .ok (LVec.xVec width)
    | some expr => E.evalExprLocals env elems st (some width) locals expr
  .ok (setAutomaticLocal locals name (value.resizeU width))

/-! ## Time-zero source statements

An `initial` block is a time-zero process (§4.7), not a cycle edge.  The first
memory wall needs only the source-shaped initialization form used by real
register files: conditional/blocking statements and a run-time `for` whose
body writes one memory cell.  It updates the existing `MemState` directly;
it does not expand cells or turn the initializer into an edge process. -/

mutual

def CoreMemDesign.writeInitialCell (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState)
    (target : PLhs) (name : String) (md : CoreMemDecl) (value : LVec) : Res CoreMemState :=
  match target with
  | .arrayElem _ [index] =>
      do
        let idx ← E.evalIndex env elems st index
        match st.memory.writeIndexId md.shape.id index.signedCast idx value with
        | some memory => .ok { st with memory }
        | none => .unsupported s!"11.5.1: memory identity for '{name}' is not present"
  | .arrayElem _ _ => .unsupported
      s!"11.5.1: memory initial target '{name}' is not one-rank"
  | _ => .unsupported "11.5.1: packed or concatenated initial target is outside this E slice"

def CoreMemDesign.execInitialStmt (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) : Nat → PStmt → Res CoreMemState
  | 0, _ => .timeout
  | fuel + 1, .localDecl _ _ _ => .ok st
  | fuel + 1, .automaticDecl _ _ _ => .ok st
  | fuel + 1, .blockingAssign name value =>
      match E.scalarTarget name with
      | none => .unsupported s!"11.5.1: scalar initial target '{name}' is undeclared"
      | some width => do
          let v ← E.evalExpr env elems st (some width) value
          .ok (E.setScalarState st name v)
  | fuel + 1, .blockingAssignL target value =>
      match target with
      | .ident name =>
          match E.scalarTarget name with
          | none => .unsupported s!"11.5.1: scalar initial target '{name}' is undeclared"
          | some width => do
              let v ← E.evalExpr env elems st (some width) value
              .ok (E.setScalarState st name v)
      | .arrayElem name [_] =>
          match E.memDecl? name with
          | none => .unsupported s!"11.5.1: memory initial target '{name}' is undeclared"
          | some md => do
              let v ← E.evalExpr env elems st (some md.shape.elemWidth) value
              E.writeInitialCell env elems st target name md v
      | .arrayElem name _ =>
          .unsupported s!"11.5.1: memory initial target '{name}' is not one-rank"
      | _ => .unsupported "11.5.1: packed or concatenated initial target is outside this E slice"
  | fuel + 1, .ifStmt cond yes no => do
      let cv ← E.evalExpr env elems st (some 1) cond
      if cv.condTrue then E.execInitialStmt env elems st fuel yes
      else match no with
        | none => .ok st
        | some stmt => E.execInitialStmt env elems st fuel stmt
  | fuel + 1, .block body => E.execInitialStmts env elems st fuel body
  | fuel + 1, .forLoop iterator init condition step body =>
      match forValues2 env iterator init condition step with
      | .timeout => .timeout
      | .unsupported e => .unsupported s!"ForLoopStatement: {e}"
      | .ok values => E.execInitialLoop env elems st fuel values body iterator
  | fuel + 1, .nbaAssign .. | fuel + 1, .nbaAssignL .. =>
      .unsupported "10.4.2: nonblocking assignment in a time-zero initializer"
  | fuel + 1, .caseStmt .. => .unsupported "12.5: case in a time-zero initializer is outside this slice"
  | fuel + 1, .unsupported kind text => .unsupported s!"{kind}: {text}"

def CoreMemDesign.execInitialStmts (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) : Nat → List PStmt → Res CoreMemState
  | 0, _ => .timeout
  | fuel + 1, [] => .ok st
  | fuel + 1, stmt :: rest => do
      let st' ← E.execInitialStmt env elems st fuel stmt
      E.execInitialStmts env elems st' fuel rest

def CoreMemDesign.execInitialLoop (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) : Nat → List Int → PStmt → String → Res CoreMemState
  | 0, _, _, _ => .timeout
  | fuel + 1, [], _, _ => .ok st
  | fuel + 1, i :: rest, body, iterator => do
      let st' ← E.execInitialStmt (env.bindVal iterator i) elems st fuel body
      E.execInitialLoop env elems st' fuel rest body iterator

end

/-! ## Plain `always @*` activations

The process starts waiting (§9.4.2.2.2).  At a slot boundary its raw reads are
compared with the state before the slot, then the retained blocking body runs
once in source order.  A body that changes one of its own watched reads would
need a second Active-region pass; that cyclic shape stays loud instead of
being silently evaluated with a stale value. -/

def CoreMemDesign.readChangedExpr (E : CoreMemDesign) (before after : CoreMemState)
    (expr : PExpr) : Res Bool :=
  if expr.hasGenvarRef && LeanModels.Sv.PExpr.hasMemoryRead expr then
    .ok true
  else do
    let old ← E.evalExpr E.env E.elems before none expr
    let now ← E.evalExpr E.env E.elems after none expr
    .ok (old != now)

def CoreMemDesign.readChanged (E : CoreMemDesign) (before after : CoreMemState)
    (reads : List PExpr) : Res Bool :=
  match reads with
  | [] => .ok false
  | expr :: rest => do
      if ← E.readChangedExpr before after expr then .ok true
      else E.readChanged before after rest

def CoreMemDesign.readChangedPure (before after : SvState) : List Expr2 → Res Bool
  | [] => .ok false
  | expr :: rest => do
      let old ← evalPure2 before expr
      let now ← evalPure2 after expr
      if old == now then CoreMemDesign.readChangedPure before after rest else .ok true

def CoreMemDesign.readChangedAt (E : CoreMemDesign)
    (before after : CoreMemState) (beforeView afterView : SvState)
    (index : Nat) (reads : List PExpr) : Res Bool :=
  match E.compiledCombReads[index]? with
  | some (some compiled) => CoreMemDesign.readChangedPure beforeView afterView compiled
  | _ => E.readChanged before after reads

def CoreMemDesign.readChangedImplicitAt (E : CoreMemDesign)
    (before after : CoreMemState) (beforeView afterView : SvState)
    (index : Nat) (reads : List PExpr) : Res Bool :=
  match E.compiledImplicitReads[index]? with
  | some (some compiled) => CoreMemDesign.readChangedPure beforeView afterView compiled
  | _ => E.readChanged before after reads

mutual

def CoreMemDesign.execImplicitStmtFuel (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) : Nat → PStmt → Res CoreMemState
  | 0, _ => .timeout
  | fuel + 1, .localDecl _ _ _ => .ok st
  | fuel + 1, .automaticDecl .. =>
      .unsupported "E implicit body does not admit automatic procedural declarations"
  | fuel + 1, .blockingAssign name value =>
      match E.scalarTarget name with
      | none => .unsupported s!"9.2.2.2: scalar implicit target '{name}' is undeclared"
      | some width => do
          let v ← E.evalExpr env elems st (some width) value
          .ok (E.setScalarState st name v)
  | fuel + 1, .blockingAssignL target value =>
      match target with
      | .ident name =>
          match E.scalarTarget name with
          | none => .unsupported s!"9.2.2.2: scalar implicit target '{name}' is undeclared"
          | some width => do
              let v ← E.evalExpr env elems st (some width) value
              .ok (E.setScalarState st name v)
      | .arrayElem name [_] =>
          match E.memDecl? name with
          | none => .unsupported s!"9.2.2.2: memory implicit target '{name}' is undeclared"
          | some md => do
              let v ← E.evalExpr env elems st (some md.shape.elemWidth) value
              E.writeInitialCell env elems st target name md v
      | .arrayElem name _ =>
          .unsupported s!"9.2.2.2: memory implicit target '{name}' is not one-rank"
      | .bitSel .. => do
          let st' ← E.execScalarTarget env elems st target value
          .ok st'
      | _ => .unsupported "9.2.2.2: packed or concatenated implicit target is outside this slice"
  | fuel + 1, .ifStmt cond yes no => do
      let cv ← E.evalExpr env elems st (some 1) cond
      if cv.condTrue then E.execImplicitStmtFuel env elems st fuel yes
      else match no with
        | none => .ok st
        | some stmt => E.execImplicitStmtFuel env elems st fuel stmt
  | fuel + 1, .block body => E.execImplicitStmtsFuel env elems st fuel body
  | fuel + 1, .forLoop .. =>
      .unsupported "9.2.2.2: procedural loop in implicit memory body is outside this slice"
  | fuel + 1, .caseStmt subject items default? mode check => do
      let sv ← E.evalExpr env elems st none subject
      match check with
      | .none =>
          let selected ← coreMemSelectCase E env elems st sv mode items default?
          match selected with
          | none => .ok st
          | some body => E.execImplicitStmtFuel env elems st fuel body
      | qualifier =>
          let n ← coreMemCaseHits E env elems st sv mode items
          if caseClaimOk qualifier default?.isSome n then
            let selected ← coreMemSelectCase E env elems st sv mode items default?
            match selected with
            | none => .ok st
            | some body => E.execImplicitStmtFuel env elems st fuel body
          else
            .unsupported s!"12.5.3: {caseCheckName qualifier}"
  | fuel + 1, .nbaAssign .. | fuel + 1, .nbaAssignL .. =>
      .unsupported "10.4.2: nonblocking assignment in implicit memory body"
  | fuel + 1, .unsupported kind text => .unsupported s!"{kind}: {text}"

def CoreMemDesign.execImplicitStmtsFuel (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) : Nat → List PStmt → Res CoreMemState
  | 0, _ => .timeout
  | fuel + 1, [] => .ok st
  | fuel + 1, stmt :: rest => do
      let st' ← E.execImplicitStmtFuel env elems st fuel stmt
      E.execImplicitStmtsFuel env elems st' fuel rest

end

def CoreMemDesign.execImplicitStmt (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) (stmt : PStmt) : Res CoreMemState :=
  E.execImplicitStmtFuel env elems st 4096 stmt

def CoreMemDesign.execImplicitStmts (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) (stmts : List PStmt) : Res CoreMemState :=
  E.execImplicitStmtsFuel env elems st 4096 stmts

/-! ## `always_comb` activations

`always_comb` has a distinct startup rule from plain `always @*`: it executes
once at time zero (§9.2.2.2), then wakes on changes to the expressions read by
the retained body (§9.2.2.2.1).  The body fragment here is deliberately the
same source-shaped blocking/conditional/blocking subset as the implicit-event
route, with the parser-native plain/inside `case` node handled by the case
matcher below.  `casez`/`casex`, NBA, loops, and unsupported statements remain
loud at their own node; no statement is lowered into a second AST. -/

def CoreMemDesign.evalCombExpr (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) (view : SvState)
    (ctx : Option Nat) (e : PExpr) : Res LVec :=
  if LeanModels.Sv.PExpr.hasTestPlusargs e then
    E.evalRuntimeExpr env elems st ctx e
  else if !LeanModels.Sv.PExpr.hasMemoryRead e && !LeanModels.Sv.PExpr.hasFunctionCall e then
    evalPure2 view (instExpr2 env elems ctx e)
  else
    E.evalExpr env elems st ctx e

mutual

def CoreMemDesign.execCombLoopValuesFuel (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) (view locals : SvState) :
    Nat → List Int → PStmt → String → Res (CoreMemState × SvState × SvState)
  | 0, _, _, _ => .timeout
  | fuel + 1, [], _, _ => .ok (st, view, locals)
  | fuel + 1, i :: rest, body, iterator => do
      let (st', view', locals') ←
        E.execCombStmtFuel (env.bindVal iterator i) elems st view locals fuel body
      E.execCombLoopValuesFuel env elems st' view' locals' fuel rest body iterator

def CoreMemDesign.execCombStmtFuel (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) (view locals : SvState) :
    Nat → PStmt → Res (CoreMemState × SvState × SvState)
  | 0, _ => .timeout
  | fuel + 1, .localDecl _ _ _ => .ok (st, view, locals)
  | fuel + 1, .automaticDecl name width init => do
      let locals' ← E.execAutomaticDecl env elems st locals name width init
      .ok (st, view, locals')
  | fuel + 1, .blockingAssign name value =>
      match SvState.lookup locals name with
      | some old => do
          let v ← if LeanModels.Sv.PExpr.hasTestPlusargs value then
            E.evalRuntimeExpr env elems st (some old.width) value
          else E.evalExprLocals env elems st (some old.width) locals value
          .ok (st, view, setAutomaticLocal locals name (v.resizeU old.width))
      | none =>
          match E.scalarTarget name with
          | none => .unsupported s!"9.2.2.2: scalar always_comb target '{name}' is undeclared"
          | some width => do
              let v ← if LeanModels.Sv.PExpr.hasTestPlusargs value then
                E.evalRuntimeExpr env elems st (some width) value
              else E.evalExprLocals env elems st (some width) locals value
              let st' := E.setScalarState st name v
              .ok (st', SvState.set view name v, locals)
  | fuel + 1, .blockingAssignL target value =>
      match target with
      | .ident name =>
          E.execCombStmtFuel env elems st view locals fuel (.blockingAssign name value)
      | .arrayElem name [_] =>
          match E.memDecl? name with
          | none => do
              let st' ← E.execScalarTarget env elems st target value
              .ok (st', E.scalar.view st'.scalar, locals)
          | some md => do
              let v ← if LeanModels.Sv.PExpr.hasTestPlusargs value then
                E.evalRuntimeExpr env elems st (some md.shape.elemWidth) value
              else E.evalExprLocals env elems st (some md.shape.elemWidth) locals value
              let st' ← E.writeInitialCell env elems st target name md v
              .ok (st', view, locals)
      | .arrayElem name _ =>
          .unsupported s!"9.2.2.2: memory always_comb target '{name}' is not one-rank"
      | .partSel name msb lsb => do
          let hi ← E.evalIndex env elems st msb
          let lo ← E.evalIndex env elems st lsb
          let some hi := hi.toNat? | .unsupported "9.2.2.2: packed part-select bound is unknown"
          let some lo := lo.toNat? | .unsupported "9.2.2.2: packed part-select bound is unknown"
          if hi < lo then
            .unsupported "9.2.2.2: packed part-select has descending runtime bounds"
          else
            let v ← if LeanModels.Sv.PExpr.hasTestPlusargs value then
              E.evalRuntimeExpr env elems st (some (hi - lo + 1)) value
            else E.evalExprLocals env elems st (some (hi - lo + 1)) locals value
            let st' ← E.writeScalarPartAssign env elems st name msb lsb v
            .ok (st', E.scalar.view st'.scalar, locals)
      | .aggregateMember base path =>
          match E.aggregateDecl? base with
          | none => .unsupported s!"9.2.2.2: aggregate always_comb target '{base}' is undeclared"
          | some decl => do
              let steps ← E.evalAggPath env elems st view path
              match decl.ty.resolve? steps with
              | none => .unsupported "9.2.2.2: aggregate always_comb target path is invalid"
              | some ty => do
                  let v ← if LeanModels.Sv.PExpr.hasTestPlusargs value then
                    E.evalRuntimeExpr env elems st (some ty.width) value
                  else E.evalExprLocals env elems st (some ty.width) locals value
                  match st.aggregates.write? decl.id steps (Val.ofLVec ty v) with
                  | none => .unsupported "9.2.2.2: aggregate always_comb target path is not writable"
                  | some aggregates' => .ok ({ st with aggregates := aggregates' }, view, locals)
      | .bitSel .. => do
          let st' ← E.execScalarTarget env elems st target value
          .ok (st', E.scalar.view st'.scalar, locals)
      | _ => .unsupported "9.2.2.2: packed or concatenated always_comb target is outside this slice"
  | fuel + 1, .ifStmt cond yes no => do
      let cv ← if LeanModels.Sv.PExpr.hasTestPlusargs cond then
        E.evalRuntimeExpr env elems st (some 1) cond
      else E.evalExprLocals env elems st (some 1) locals cond
      if cv.condTrue then E.execCombStmtFuel env elems st view locals fuel yes
      else match no with
        | none => .ok (st, view, locals)
        | some stmt => E.execCombStmtFuel env elems st view locals fuel stmt
  | fuel + 1, .block body => E.execCombStmtsFuel env elems st view locals fuel body
  | fuel + 1, .forLoop iterator init condition step body =>
      match forValues2 env iterator init condition step with
      | .timeout => .timeout
      | .unsupported e => .unsupported s!"ForLoopStatement: {e}"
      | .ok values => E.execCombLoopValuesFuel env elems st view locals fuel values body iterator
  | fuel + 1, .caseStmt subject items default? mode check => do
      let sv ← E.evalExprLocals env elems st none locals subject
      match check with
      | .none =>
          let selected ← coreMemSelectCase E env elems st sv mode items default?
          match selected with
          | none => .ok (st, view, locals)
          | some body => E.execCombStmtFuel env elems st view locals fuel body
      | qualifier =>
          let n ← coreMemCaseHits E env elems st sv mode items
          if caseClaimOk qualifier default?.isSome n then
            let selected ← coreMemSelectCase E env elems st sv mode items default?
            match selected with
            | none => .ok (st, view, locals)
            | some body => E.execCombStmtFuel env elems st view locals fuel body
          else
            .unsupported s!"12.5.3: {caseCheckName qualifier}"
  | fuel + 1, .nbaAssign .. | fuel + 1, .nbaAssignL .. =>
      .unsupported "10.4.2: nonblocking assignment in always_comb body"
  | fuel + 1, .unsupported kind text => .unsupported s!"{kind}: {text}"

def CoreMemDesign.execCombStmtsFuel (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) (view locals : SvState) :
    Nat → List PStmt → Res (CoreMemState × SvState × SvState)
  | 0, _ => .timeout
  | fuel + 1, [] => .ok (st, view, locals)
  | fuel + 1, stmt :: rest => do
      let (st', view', locals') ← E.execCombStmtFuel env elems st view locals fuel stmt
      E.execCombStmtsFuel env elems st' view' locals' fuel rest

end

def CoreMemDesign.execCombStmtAtView (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) (view : SvState) (stmt : PStmt) :
    Res (CoreMemState × SvState) :=
  do
    let (st', view', _) ← E.execCombStmtFuel env elems st view [] 4096 stmt
    .ok (st', view')

def CoreMemDesign.execCombStmt (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) (stmt : PStmt) : Res CoreMemState :=
  do
    let (st', view') ← E.execCombStmtAtView env elems st (E.scalar.view st.scalar) stmt
    .ok (E.compactScalar st' view')


def CoreMemDesign.runImplicitAt (E : CoreMemDesign) (before current : CoreMemState)
    (beforeView currentView : SvState) (index : Nat) :
    List CoreMemProc → Res CoreMemState
  | [] => .ok current
  | .primitive _ _ _ :: rest =>
      E.runImplicitAt before current beforeView currentView (index + 1) rest
  | .implicit body :: rest => do
      let reads := coreMemExternalReadExprs body
      let ready ← E.readChangedImplicitAt before current beforeView currentView index reads
      if !ready then
        E.runImplicitAt before current beforeView currentView (index + 1) rest
      else
        let after ← E.execImplicitStmt E.env E.elems current body
        let afterView := E.scalar.view after.scalar
        let rearmed ← E.readChangedImplicitAt current after currentView afterView index reads
        if rearmed then
          .unsupported
            "ProceduralBlockSymbol:Always: implicit event process re-triggered in one active pass"
        else
          E.runImplicitAt before after beforeView afterView (index + 1) rest
  | .event _ _ :: rest => E.runImplicitAt before current beforeView currentView (index + 1) rest
  | .assign _ _ :: rest => E.runImplicitAt before current beforeView currentView (index + 1) rest
  | .edge _ :: rest => E.runImplicitAt before current beforeView currentView (index + 1) rest
  | .initial _ :: rest => E.runImplicitAt before current beforeView currentView (index + 1) rest
  | .comb _ :: rest => E.runImplicitAt before current beforeView currentView (index + 1) rest
  | .latch _ :: rest => E.runImplicitAt before current beforeView currentView (index + 1) rest
  | .unsupported kind text :: _ => .unsupported s!"{kind}: {text}"

def CoreMemDesign.runImplicitPass (E : CoreMemDesign) (before current : CoreMemState) :
    List CoreMemProc → Res CoreMemState := fun procs =>
  E.runImplicitAt before current (E.scalar.view before.scalar)
    (E.scalar.view current.scalar) 0 procs

/-! Plain `always @*` processes are scheduled in the active region.  A
source-order pass can wake a process that appeared earlier in the source, as
in `y = t;` followed by `t = a;`.  Re-run the retained processes until the
scalar view is unchanged.  The bound is a loud guard for oscillating reactive
regions, so no simulator-specific fixed point is selected. -/
def CoreMemDesign.runImplicitQuiesce (E : CoreMemDesign) (limit : Nat)
    (before current : CoreMemState) (procs : List CoreMemProc) : Res CoreMemState :=
  match limit with
  | 0 => .unsupported "4.5: implicit event region did not quiesce within the canonical E bound"
  | n + 1 => do
      let next ← E.runImplicitPass before current procs
      let beforeView := E.scalar.view before.scalar
      let nextView := E.scalar.view next.scalar
      if beforeView == nextView then
        .ok next
      else
        E.runImplicitQuiesce n current next procs

def CoreMemDesign.runImplicit (E : CoreMemDesign) (before current : CoreMemState) :
    List CoreMemProc → Res CoreMemState := fun procs =>
  E.runImplicitQuiesce 4096 before current procs

def CoreMemDesign.runCombInitialWithView (E : CoreMemDesign) (current : CoreMemState)
    (view : SvState) : List CoreMemProc → Res (CoreMemState × SvState)
  | [] => .ok (current, view)
  | .primitive _ _ _ :: rest => E.runCombInitialWithView current view rest
  | .comb body :: rest => do
      let (after, view') ← E.execCombStmtAtView E.env E.elems current view body
      E.runCombInitialWithView (E.compactScalar after view') view' rest
  | .latch body :: rest => do
      let (after, view') ← E.execCombStmtAtView E.env E.elems current view body
      E.runCombInitialWithView (E.compactScalar after view') view' rest
  | _ :: rest => E.runCombInitialWithView current view rest

def CoreMemDesign.runCombInitial (E : CoreMemDesign) (current : CoreMemState) :
    List CoreMemProc → Res CoreMemState := fun procs => do
  let (after, _) ← E.runCombInitialWithView current (E.scalar.view current.scalar) procs
  .ok after

def CoreMemDesign.runCombInitialQuiesce (E : CoreMemDesign) (limit : Nat)
    (current : CoreMemState) (procs : List CoreMemProc) : Res CoreMemState :=
  match limit with
  | 0 => .unsupported "4.5: always_comb startup region did not quiesce within the canonical E bound"
  | n + 1 => do
      let next ← E.runCombInitial current procs
      let beforeView := E.scalar.view current.scalar
      let nextView := E.scalar.view next.scalar
      if beforeView == nextView then
        .ok next
      else
        E.runCombInitialQuiesce n next procs

def CoreMemDesign.runCombAt (E : CoreMemDesign) (before : CoreMemState)
    (beforeView : SvState) (current : CoreMemState) (currentView : SvState)
    (index : Nat) : List CoreMemProc → Res CoreMemState
  | [] => .ok current
  | .primitive _ _ _ :: rest => E.runCombAt before beforeView current currentView (index + 1) rest
  | .comb body :: rest => do
      let reads := coreMemCombExternalReadExprs body
      let ready ← E.readChangedAt before current beforeView currentView index reads
      if !ready then
        E.runCombAt before beforeView current currentView (index + 1) rest
      else
        let (after, afterView) ←
          E.execCombStmtAtView E.env E.elems current currentView body
        let after := E.compactScalar after afterView
        E.runCombAt before beforeView after afterView (index + 1) rest
  | .assign _ _ :: rest => E.runCombAt before beforeView current currentView (index + 1) rest
  | .edge _ :: rest => E.runCombAt before beforeView current currentView (index + 1) rest
  | .initial _ :: rest => E.runCombAt before beforeView current currentView (index + 1) rest
  | .implicit _ :: rest => E.runCombAt before beforeView current currentView (index + 1) rest
  | .event _ _ :: rest => E.runCombAt before beforeView current currentView (index + 1) rest
  | .latch body :: rest => do
      let reads := coreMemExternalReadExprs body
      let ready ← E.readChangedAt before current beforeView currentView index reads
      if !ready then
        E.runCombAt before beforeView current currentView (index + 1) rest
      else
        let (after, afterView) ← E.execCombStmtAtView E.env E.elems current currentView body
        let after := E.compactScalar after afterView
        E.runCombAt before beforeView after afterView (index + 1) rest
  | .unsupported kind text :: _ => .unsupported s!"{kind}: {text}"

def CoreMemDesign.runCombPass (E : CoreMemDesign) (before current : CoreMemState) :
    List CoreMemProc → Res CoreMemState := fun procs =>
  E.runCombAt before (E.scalar.view before.scalar) current
    (E.scalar.view current.scalar) 0 procs

def CoreMemDesign.runCombQuiesce (E : CoreMemDesign) (limit : Nat)
    (before current : CoreMemState) (procs : List CoreMemProc) : Res CoreMemState :=
  match limit with
  | 0 => .unsupported "4.5: always_comb region did not quiesce within the canonical E bound"
  | n + 1 => do
      let next ← E.runCombPass before current procs
      let beforeView := E.scalar.view before.scalar
      let nextView := E.scalar.view next.scalar
      if beforeView == nextView then
        .ok next
      else
        E.runCombQuiesce n current next procs

def CoreMemDesign.runComb (E : CoreMemDesign) (before current : CoreMemState) :
    List CoreMemProc → Res CoreMemState := fun procs =>
  E.runCombQuiesce 4096 before current procs

/- A blocking edge write updates the retained state immediately.  The same
one-rank source-shaped memory target used by the initializer and combinational
routes is accepted here; NBA targets continue through `issueTarget` below. -/
def CoreMemDesign.execBlockingTarget (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) (target : PLhs)
    (value : PExpr) : Res CoreMemState :=
  match target with
  | .ident name =>
      match E.scalarTarget name with
      | none => .unsupported s!"9.2.2.1: scalar edge target '{name}' is undeclared"
      | some width => do
          let v ← E.evalExpr env elems st (some width) value
          .ok (E.setScalarState st name v)
  | .arrayElem name indices =>
      match E.memDecl? name with
      | none => E.execScalarTarget env elems st (.arrayElem name indices) value
      | some md =>
          match indices with
          | [_] => do
              let v ← E.evalExpr env elems st (some md.shape.elemWidth) value
              E.writeInitialCell env elems st target name md v
          | _ => .unsupported s!"9.2.2.1: memory edge target '{name}' is not one-rank"
  | target => E.execScalarTarget env elems st target value

def CoreMemDesign.execBlockingIdentLocal (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) (locals : SvState)
    (name : String) (value : PExpr) : Res (CoreMemState × SvState) :=
  match SvState.lookup locals name with
  | some old => do
      let v ← E.evalExprLocals env elems st (some old.width) locals value
      .ok (st, setAutomaticLocal locals name (v.resizeU old.width))
  | none => do
      let st' ← E.execBlockingTarget env elems st (.ident name) value
      .ok (st', locals)

mutual

def CoreMemDesign.execStmtFuel (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (locals : SvState) : Nat → PStmt → CoreMemExec
  | 0, _ => .timeout
  | fuel + 1, .localDecl _ _ _ => .ok { state := st, scalarQ := [], memoryQ := [], locals }
  | fuel + 1, .automaticDecl name width init => do
      let locals' ← E.execAutomaticDecl env elems st locals name width init
      .ok { state := st, scalarQ := [], memoryQ := [], locals := locals' }
  | fuel + 1, .nbaAssign target value =>
      match SvState.lookup locals target with
      | some _ => .unsupported "10.4.2: nonblocking assignment to an automatic local is outside this E activation"
      | none =>
          match E.scalarTarget target with
          | none => .unsupported s!"11.5.1: scalar NBA target '{target}' is undeclared"
          | some width => do
              let v ← E.evalExprLocals env elems st (some width) locals value
              CoreMemExec.withLocals locals (CoreMemExec.fromQueue st (E.issueTarget env elems st (.ident target) v))
  | fuel + 1, .nbaAssignL target value =>
      match target with
      | .ident name =>
          match SvState.lookup locals name with
          | some _ => .unsupported "10.4.2: nonblocking assignment to an automatic local is outside this E activation"
          | none =>
              match E.scalarTarget name with
              | none => .unsupported s!"11.5.1: scalar NBA target '{name}' is undeclared"
              | some width => do
                  let v ← E.evalExprLocals env elems st (some width) locals value
                  CoreMemExec.withLocals locals (CoreMemExec.fromQueue st (E.issueTarget env elems st target v))
      | .arrayElem name indices =>
          match E.memDecl? name with
          | none => do
              let (_, width) ← E.scalarLhs2 env elems target
              let v ← E.evalExprLocals env elems st (some width) locals value
              CoreMemExec.withLocals locals (CoreMemExec.fromQueue st (E.issueScalarTarget env elems st target v))
          | some md =>
              match indices with
              | [_] => do
                  let v ← E.evalExprLocals env elems st (some md.shape.elemWidth) locals value
                  CoreMemExec.withLocals locals (CoreMemExec.fromQueue st (E.issueTarget env elems st target v))
              | _ => .unsupported s!"11.5.1: memory target '{name}' is not one-rank"
      | target => do
          let (_, width) ← E.scalarLhs2 env elems target
          let v ← E.evalExprLocals env elems st (some width) locals value
          CoreMemExec.withLocals locals (CoreMemExec.fromQueue st (E.issueScalarTarget env elems st target v))
  | fuel + 1, .blockingAssign name value => do
      let (st', locals') ← E.execBlockingIdentLocal env elems st locals name value
      .ok { state := st', scalarQ := [], memoryQ := [], locals := locals' }
  | fuel + 1, .blockingAssignL target value =>
      match target with
      | .ident name => do
          let (st', locals') ← E.execBlockingIdentLocal env elems st locals name value
          .ok { state := st', scalarQ := [], memoryQ := [], locals := locals' }
      | _ => do
          let st' ← E.execBlockingTarget env elems st target value
          .ok { state := st', scalarQ := [], memoryQ := [], locals }
  | fuel + 1, .ifStmt cond yes no => do
      let cv ← E.evalExprLocals env elems st (some 1) locals cond
      if cv.condTrue then E.execStmtFuel env elems st locals fuel yes
      else match no with
        | none => .ok { state := st, scalarQ := [], memoryQ := [], locals }
        | some s => E.execStmtFuel env elems st locals fuel s
  | fuel + 1, .block body => E.execStmtsFuel env elems st locals fuel body
  | fuel + 1, .forLoop iterator init condition step body =>
      match forValues2 env iterator init condition step with
      | .timeout => .timeout
      | .unsupported e => .unsupported s!"ForLoopStatement: {e}"
      | .ok values => E.execLoopValuesFuel env elems st locals fuel values body iterator
  | fuel + 1, .caseStmt subject items default? mode check => do
      let sv ← E.evalExprLocals env elems st none locals subject
      match check with
      | .none =>
          let selected ← coreMemSelectCase E env elems st sv mode items default?
          match selected with
          | none => .ok { state := st, scalarQ := [], memoryQ := [], locals }
          | some body => E.execStmtFuel env elems st locals fuel body
      | qualifier =>
          let n ← coreMemCaseHits E env elems st sv mode items
          if caseClaimOk qualifier default?.isSome n then
            let selected ← coreMemSelectCase E env elems st sv mode items default?
            match selected with
            | none => .ok { state := st, scalarQ := [], memoryQ := [], locals }
            | some body => E.execStmtFuel env elems st locals fuel body
          else
            .unsupported s!"12.5.3: {caseCheckName qualifier}"
  | fuel + 1, .unsupported kind text => .unsupported s!"{kind}: {text}"

def CoreMemDesign.execStmtsFuel (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (locals : SvState) : Nat → List PStmt → CoreMemExec
  | 0, _ => .timeout
  | fuel + 1, [] => .ok { state := st, scalarQ := [], memoryQ := [], locals }
  | fuel + 1, stmt :: rest => do
      let a ← E.execStmtFuel env elems st locals fuel stmt
      let b ← E.execStmtsFuel env elems a.state a.locals fuel rest
      .ok (CoreMemExec.append a b)

def CoreMemDesign.execLoopValuesFuel (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (locals : SvState) : Nat → List Int → PStmt → String → CoreMemExec
  | 0, _, _, _ => .timeout
  | fuel + 1, [], _, _ => .ok { state := st, scalarQ := [], memoryQ := [], locals }
  | fuel + 1, i :: rest, body, iterator => do
      let a ← E.execStmtFuel (env.bindVal iterator i) elems st locals fuel body
      let b ← E.execLoopValuesFuel env elems a.state a.locals fuel rest body iterator
      .ok (CoreMemExec.append a b)

end

def CoreMemDesign.execStmt (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (stmt : PStmt) : CoreMemExec :=
  E.execStmtFuel env elems st [] 4096 stmt

def CoreMemDesign.execStmts (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (stmts : List PStmt) : CoreMemExec :=
  E.execStmtsFuel env elems st [] 4096 stmts

def CoreMemDesign.execLoopValues (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (values : List Int) (body : PStmt) (iterator : String) : CoreMemExec :=
  E.execLoopValuesFuel env elems st [] 4096 values body iterator

/-! ## Slots, scalar E commit, and memory commit -/

def CoreMemEdge.fires (p : CoreMemEdge) (before after : SvState) : Bool :=
  (match p.edge with
   | .posedge => isPosedge (before.bit0 p.clock) (after.bit0 p.clock)
   | .negedge => isNegedge (before.bit0 p.clock) (after.bit0 p.clock)) ||
    match p.reset with
    | none => false
    | some r => if p.resetHigh then
        isPosedge (before.bit0 r) (after.bit0 r)
      else
        isNegedge (before.bit0 r) (after.bit0 r)

/-- A retained edge or one-clock plain `always` event process fires across a
state change. Event lists use the same IEEE edge table as edge processes. -/
def CoreMemProc.firesIn (a b : SvState) : CoreMemProc → Bool
  | .edge q => q.fires a b
  | .event events _ => coreMemEventsFire a b events
  | _ => false

def CoreMemDesign.settleAssignAt (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (view : SvState) (index : Nat) : List CoreMemProc →
    Res (CoreMemState × SvState)
  | [] => .ok (st, view)
  | .primitive op target inputs :: rest =>
      match target, inputs with
      | .ident name, [left, right] => do
          let width ← match E.scalarWidth? name with
            | some w => .ok w
            | none => .unsupported s!"28: primitive target '{name}' is undeclared"
          let a ← E.evalExprLocals env elems st none view left
          let b ← E.evalExprLocals env elems st none view right
          let value := match op with
            | "and" => evalBinOp .land a b
            | "or" => evalBinOp .lor a b
            | "xor" => evalBinOp .xor a b
            | "xnor" => evalUnaryOp .bnot (evalBinOp .xor a b)
            | _ => LVec.xVec width
          let st' := E.setScalarState st name (value.resizeU width)
          E.settleAssignAt env elems st' (E.scalar.view st'.scalar) (index + 1) rest
      | _, _ => .unsupported s!"28: unsupported primitive '{op}' arity or target"
  | .assign target value :: rest => do
      match target with
      | .ident name =>
          let width ← match E.scalarWidth? name with
            | some w => .ok w
            | none => .unsupported s!"10.3: continuous target '{name}' is undeclared"
          let v ← E.evalScalarAssignAtView env elems st view (some width) index value
          let resolved := if E.resolvedNets.contains name then
              LVec.resolveDrivers [
                (SvState.lookup view name).getD (LVec.replicate width .lz), v]
            else v
          let st' := E.setScalarState st name resolved
          E.settleAssignAt env elems st' (SvState.set view name resolved) (index + 1) rest
      | .bitSel name select =>
          let st' ← E.writeScalarBitAssign env elems st name select value
          let view' := E.scalar.view st'.scalar
          E.settleAssignAt env elems st' view' (index + 1) rest
      | .partSel name msb lsb =>
          let width ← match E.scalarWidth? name with
            | some w => .ok w
            | none => .unsupported s!"10.3: scalar target '{name}' is undeclared"
          let hi ← E.evalIndex env elems st msb
          let lo ← E.evalIndex env elems st lsb
          let some hi := hi.toNat? | .unsupported "10.3: packed part-select bound is unknown"
          let some lo := lo.toNat? | .unsupported "10.3: packed part-select bound is unknown"
          if hi < lo || hi >= width then
            .unsupported "10.3: packed part-select bounds are outside the scalar target"
          else
            let w := hi - lo + 1
            let v ← E.evalScalarAssignAtView env elems st view (some w) index value
            let st' ← E.writeScalarPartAssign env elems st name msb lsb v
            let view' := E.scalar.view st'.scalar
            E.settleAssignAt env elems st' view' (index + 1) rest
      | .arrayPart name [] .range msb lsb =>
          let width ← match E.scalarWidth? name with
            | some w => .ok w
            | none => .unsupported s!"10.3: scalar target '{name}' is undeclared"
          let hi ← E.evalIndex env elems st msb
          let lo ← E.evalIndex env elems st lsb
          let some hi := hi.toNat? | .unsupported "10.3: packed part-select bound is unknown"
          let some lo := lo.toNat? | .unsupported "10.3: packed part-select bound is unknown"
          if hi < lo || hi >= width then
            .unsupported "10.3: packed part-select bounds are outside the scalar target"
          else
            let w := hi - lo + 1
            let v ← E.evalScalarAssignAtView env elems st view (some w) index value
            let st' ← E.writeScalarPartAssign env elems st name msb lsb v
            let view' := E.scalar.view st'.scalar
            E.settleAssignAt env elems st' view' (index + 1) rest
      | .arrayPart name [] mode base widthExpr =>
          let width ← match E.scalarWidth? name with
            | some w => .ok w
            | none => .unsupported s!"10.3: scalar target '{name}' is undeclared"
          let bv ← E.evalIndex env elems st base
          let wv ← E.evalIndex env elems st widthExpr
          let some b := bv.toNat? | .unsupported "10.3: indexed part-select base is unknown"
          let some w := wv.toNat? | .unsupported "10.3: indexed part-select width is unknown"
          if w == 0 then
            .unsupported "10.3: indexed part-select has zero width"
          else
            let bounds := match mode with
              | .up => if b + w - 1 < width then some (b, b + w - 1) else none
              | .down => if b + 1 >= w && b < width then some (b - w + 1, b) else none
              | .range => none
            match bounds with
            | none => .unsupported "10.3: indexed part-select bounds are outside the scalar target"
            | some (lo, _) =>
                let v ← E.evalScalarAssignAtView env elems st view (some w) index value
                match E.scalar.resolve name with
                | some x =>
                    let old := st.scalar x
                    let st' := E.setScalarState st name
                      (old.bits.insertAt lo (v.resizeU w))
                    let view' := E.scalar.view st'.scalar
                    E.settleAssignAt env elems st' view' (index + 1) rest
                | none => .unsupported s!"10.3: scalar target '{name}' is undeclared"
      | .arrayElem target [] =>
          (match value with
           | .arrayElem source [] =>
               match E.copyMemoryAssign st target source with
               | .ok st' => E.settleAssignAt env elems st' view (index + 1) rest
               | .timeout => .timeout
               | .unsupported msg => .unsupported msg
           | _ => .unsupported
               "23.3.3: unpacked port connection actual is not a whole array")
      | .arrayElem name [_] =>
          match E.memDecl? name with
          | none =>
              -- Slang uses `ArraySel` for a packed bit-select written with
              -- the source spelling `name[index]`.  When the declaration is
              -- scalar storage, this is the same packed target handled by
              -- the parser-native `.bitSel` arm above, not an unpacked
              -- memory target.  Preserve the source node and dispatch to the
              -- scalar four-state update instead of reporting a false §10.3
              -- undeclared-memory refusal.
              match E.scalarWidth? name with
              | some _ =>
                  let st' ← E.writeScalarBitAssign env elems st name (match target with
                    | .arrayElem _ [ix] => ix
                    | _ => .int 0) value
                  let view' := E.scalar.view st'.scalar
                  E.settleAssignAt env elems st' view' (index + 1) rest
              | none => .unsupported s!"10.3: continuous memory target '{name}' is undeclared"
          | some md =>
              let v ← E.evalExpr env elems st (some md.shape.elemWidth) value
              let st' ← E.writeMemoryAssign env elems st target md v
              E.settleAssignAt env elems st' view (index + 1) rest
      | _ => .unsupported "10.3: packed or multi-rank continuous memory target is outside this slice"
  | .edge _ :: rest => E.settleAssignAt env elems st view (index + 1) rest
  | .initial _ :: rest => E.settleAssignAt env elems st view (index + 1) rest
  | .comb _ :: rest => E.settleAssignAt env elems st view (index + 1) rest
  | .implicit _ :: rest => E.settleAssignAt env elems st view (index + 1) rest
  | .event _ _ :: rest => E.settleAssignAt env elems st view (index + 1) rest
  | .latch _ :: rest => E.settleAssignAt env elems st view (index + 1) rest
  | .unsupported kind text :: _ =>
      .unsupported s!"{kind}: {text}"

def CoreMemDesign.settleAssign (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (procs : List CoreMemProc) : Res CoreMemState :=
  do
    let st0 := E.resetResolvedNets st
    let (st', view') ← E.settleAssignAt env elems st0 (E.scalar.view st0.scalar) 0 procs
    .ok (E.compactScalar st' view')

/-- Re-run the continuous-assignment region until its settled view stops changing.
IEEE 1800-2023 §§4.5 and 10.3 permit source orders that are not topological;
the active region remains live while a driver update causes another driver to
become current.  A bounded run is a loud refusal on a combinational loop, never
a truncated answer. -/
def CoreMemDesign.settleAssignQuiesce (E : CoreMemDesign) (limit : Nat)
    (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (procs : List CoreMemProc) : Res CoreMemState :=
  match limit with
  | 0 => .unsupported "4.5: continuous-assignment region did not quiesce within the canonical E bound"
  | n + 1 => do
      let before := E.scalar.view st.scalar
      let next ← E.settleAssign env elems st procs
      let after := E.scalar.view next.scalar
      if before == after then
        .ok next
      else
        E.settleAssignQuiesce n env elems next procs

def CoreMemDesign.settleCanonical (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (procs : List CoreMemProc) : Res CoreMemState :=
  E.settleAssignQuiesce 4096 env elems st procs

/-! Continuous assignments and procedural combinational blocks share the
active region.  A combinational block can therefore change a continuous
assignment's source, which in turn must wake a later combinational block in
the same slot.  The ordinary `runComb` fixed point only observes procedural
updates, so this wrapper alternates its retained comb pass with the
source-shaped continuous-assignment settle until both regions are quiet
(IEEE 1800-2023 §4.5). -/
def CoreMemDesign.runCombSettleQuiesce (E : CoreMemDesign) (limit : Nat)
    (before current : CoreMemState) (procs : List CoreMemProc) : Res CoreMemState :=
  match limit with
  | 0 => .unsupported "4.5: combinational and continuous regions did not quiesce within the canonical E bound"
  | n + 1 => do
      let combed ← E.runComb before current procs
      let settled ← E.settleCanonical E.env E.elems combed procs
      let beforeView := E.scalar.view current.scalar
      let settledView := E.scalar.view settled.scalar
      if beforeView == settledView then
        .ok settled
      else
        E.runCombSettleQuiesce n combed settled procs

def CoreMemDesign.settleAssignWithView (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) (view : SvState)
    (procs : List CoreMemProc) :
    Res (CoreMemState × SvState) :=
  do
    let st0 := E.resetResolvedNets st
    let view0 := E.scalar.view st0.scalar
    let (st', view') ← E.settleAssignAt env elems st0 view0 0 procs
    .ok (E.compactScalar st' view', view')

/-! Structured `$readmemh` initialization (§21.4).  The extractor has already
read and validated the literal words into `PReadmemh`; this route consumes
that typed metadata and never opens a host file. -/
def coreMemHexDigit (c : Char) : Option Nat :=
  if c >= '0' && c <= '9' then some (c.toNat - '0'.toNat)
  else if c >= 'a' && c <= 'f' then some (10 + c.toNat - 'a'.toNat)
  else if c >= 'A' && c <= 'F' then some (10 + c.toNat - 'A'.toNat)
  else none

def coreMemHexNat (s : String) : Option Nat :=
  if s.isEmpty then none
  else s.toList.foldlM (init := 0) fun n c => do
    let digit ← coreMemHexDigit c
    some (n * 16 + digit)

def CoreMemDesign.writeReadmemhMem (E : CoreMemDesign) (st : CoreMemState) (task : PReadmemh)
    (md : CoreMemDecl) (index step : Int) : List String → Res CoreMemState
  | [] => .ok st
  | word :: rest =>
      match coreMemHexNat word with
      | none => .unsupported "SystemTask:readmemh:xz-digit"
      | some n =>
          let target := PLhs.arrayElem md.source.name [.int index]
          match MemState.writeTarget E.env md.source target
              (LVec.ofNat md.shape.elemWidth n) st.memory with
          | .error e => .unsupported e
          | .ok none => .unsupported "SystemTask:readmemh target is outside the memory shape"
          | .ok (some memory) =>
              E.writeReadmemhMem { st with memory } task md (index + step) step rest

def CoreMemDesign.writeReadmemh (E : CoreMemDesign) (st : CoreMemState)
    (task : PReadmemh) : Res CoreMemState :=
  match E.memDecl? task.target with
  | none => .unsupported s!"SystemTask:readmemh target '{task.target}' is not a declared memory"
  | some md =>
      let shape := md.shape
      let count := (Int.natAbs (shape.msb - shape.lsb)) + 1
      if task.words.length != count then
        .unsupported s!"SystemTask:readmemh:short-file: {task.words.length} words for {count} cells"
      else
        let step : Int := if shape.lsb >= shape.msb then 1 else -1
        E.writeReadmemhMem st task md shape.msb step task.words

def CoreMemDesign.writeReadmemhList (E : CoreMemDesign) (st : CoreMemState) :
    List PReadmemh → Res CoreMemState
  | [] => .ok st
  | task :: rest => do
      let st' ← E.writeReadmemh st task
      E.writeReadmemhList st' rest

/-! A runtime initial task cannot be selected by a two-valued branch test.
Unknown inputs leave the branch outcome open under IEEE 1800-2023 §6.3.1, so
the zero-delay E entry refuses a source-shaped system task before evaluating
the body instead of choosing the simulator's x-optimistic branch. -/
mutual

def initialRuntimeTask : PStmt → Option String
  | .unsupported kind text =>
      if kind.startsWith "SysCall:" then some s!"{kind}: {text}" else none
  | .block body => initialRuntimeTaskList body
  | .ifStmt _ yes no =>
      match initialRuntimeTask yes with
      | some msg => some msg
      | none => match no with
          | some branch => initialRuntimeTask branch
          | none => none
  | .caseStmt _ items default? _ _ =>
      match initialRuntimeTaskCases items with
      | some msg => some msg
      | none => match default? with
          | some branch => initialRuntimeTask branch
          | none => none
  | _ => none

def initialRuntimeTaskList : List PStmt → Option String
  | [] => none
  | stmt :: rest =>
      match initialRuntimeTask stmt with
      | some msg => some msg
      | none => initialRuntimeTaskList rest

def initialRuntimeTaskCases : List (List PExpr × PStmt) → Option String
  | [] => none
  | (_, body) :: rest =>
      match initialRuntimeTask body with
      | some msg => some msg
      | none => initialRuntimeTaskCases rest

end

def CoreMemDesign.execDeclInitializers (E : CoreMemDesign) (st : CoreMemState) :
    List (String × PExpr × Nat) → Res CoreMemState
  | [] => .ok st
  | (name, expr, width) :: rest => do
      let value ← E.evalExpr E.env E.elems st (some width) expr
      let st' := E.setScalarState st name value
      E.execDeclInitializers st' rest

def CoreMemDesign.initialState (E : CoreMemDesign) : Res CoreMemState := do
  let bodies := E.processes.toList.filterMap fun p =>
    match p with
    | .initial body => some body
    | _ => none
  let declared ← E.execDeclInitializers E.initial E.declInitializers
  let base0 ← if !E.readmemh.isEmpty then
    match bodies with
    | [_] => E.writeReadmemhList declared E.readmemh
    | [] => .unsupported "SystemTask:readmemh metadata has no initial process"
    | _ => .unsupported "SystemTask:readmemh: multiple initial processes are outside this cycle entry"
  else match bodies with
    | [] => .ok declared
    | [body] =>
        match initialRuntimeTask body with
        | some msg => .unsupported s!"Initial:runtime: {msg}"
        | none => E.execInitialStmt E.env E.elems E.initial 4096 body
    | _ => .unsupported "T2:Initial: multiple initial processes are outside this cycle entry"
  let base := base0
  -- The time-zero active region is the same continuous-assignment region as a
  -- slot.  It must quiesce rather than take one source-order pass: IEEE
  -- 1800-2023 §§4.5 and 10.3 permit a driver to update a later assignment,
  -- which can then update an earlier one in the same time slot.
  let settled ← E.settleCanonical E.env E.elems base E.processes.toList
  if !E.hasComb then
    .ok settled
  else
    let (settled, settledView) ←
      E.settleAssignWithView E.env E.elems base (E.scalar.view base.scalar) E.processes.toList
    let combed ← E.runCombInitialQuiesce 4096 settled E.processes.toList
    let combedView := E.scalar.view combed.scalar
    let (final, _) ← E.settleAssignWithView E.env E.elems combed combedView E.processes.toList
    .ok final

def CoreMemDesign.runEdges (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (before after : SvState) : List CoreMemProc → CoreMemExec
  | [] => .ok { state := st, scalarQ := [], memoryQ := [] }
  | .edge p :: rest =>
      if p.fires before after then do
        let a ← E.execStmt env elems st p.body
        let b ← E.runEdges env elems a.state before after rest
        .ok (CoreMemExec.append a b)
      else E.runEdges env elems st before after rest
  | .event events body :: rest =>
      if coreMemEventsFire before after events then do
        let a ← E.execStmt env elems st body
        let b ← E.runEdges env elems a.state before after rest
        .ok (CoreMemExec.append a b)
      else E.runEdges env elems st before after rest
  | .initial _ :: rest => E.runEdges env elems st before after rest
  | .implicit _ :: rest => E.runEdges env elems st before after rest
  | _ :: rest => E.runEdges env elems st before after rest

def CoreMemDesign.applyMemoryInputs (E : CoreMemDesign) (entry : SvState)
    (memory : MemState) : MemState :=
  E.memories.toList.foldl (fun mem md =>
    if !md.source.isInput then mem else
      let count := (Int.natAbs (md.shape.msb - md.shape.lsb)) + 1
      (List.range count).foldl (fun m k =>
        let ki : Int := Int.ofNat k
        let i := if md.shape.lsb >= md.shape.msb then md.shape.msb + ki else md.shape.msb - ki
        match SvState.lookup entry (md.source.name ++ "[" ++ toString i ++ "]") with
        | none => m
        | some v => (m.writeId md.shape.id i (md.shape.convert v)).getD m) mem) memory

/-- One edge/NBA/settle pass.  `edgeQuiesce` iterates this source-shaped pass
when its committed view causes another event in the same slot. -/
def CoreMemDesign.edgePass (E : CoreMemDesign)
    (st : CoreMemState) (before after : SvState) (combBefore : CoreMemState) : Res CoreMemState := do
  let edge ← E.runEdges E.env E.elems st before after E.processes.toList
  let committedStore := E.scalarEdge.commit edge.state.scalar edge.scalarQ
  let memory ← match edge.state.memory.commitNba edge.memoryQ with
    | some m => .ok m
    | none => .unsupported "10.4.2: memory NBA commit lost its declaration identity"
  let committed := E.normalizeScalar edge.state committedStore
  let settled ← E.settleCanonical E.env E.elems { committed with memory } E.processes.toList
  let activated ← if E.hasImplicit then
      E.runImplicit st settled E.processes.toList
    else .ok settled
  let combed ← if E.hasComb then
      E.runCombSettleQuiesce 4096 combBefore activated E.processes.toList
    else E.settleCanonical E.env E.elems activated E.processes.toList
  .ok combed

/-- Run edge/NBA/settle passes until the commit causes no further edge event.
IEEE 1800-2023 §§4.4 and 4.5 schedule NBA-caused events in the same time slot.
The bound is an executor guard: exhaustion is a loud refusal, never a truncated
trace. -/
def CoreMemDesign.edgeQuiesce (E : CoreMemDesign) (limit : Nat)
    (st : CoreMemState) (before after : SvState) (combBefore : CoreMemState) : Res CoreMemState :=
  match limit with
  | 0 => .unsupported "4.5: event slot did not quiesce within the canonical E bound"
  | n + 1 => do
      let next ← E.edgePass st before after combBefore
      let nextView := E.scalar.view next.scalar
      let caused := E.processes.toList.any (CoreMemProc.firesIn after nextView)
      if caused then E.edgeQuiesce n next after nextView next
      else .ok next

theorem CoreMemDesign.edgeQuiesce_succ_of_no_followup
    {E : CoreMemDesign} {n : Nat} {st next combBefore : CoreMemState} {before after : SvState}
    (hp : E.edgePass st before after combBefore = .ok next)
    (hc : E.processes.toList.any
      (CoreMemProc.firesIn after (E.scalar.view next.scalar)) = false) :
    E.edgeQuiesce (n + 1) st before after combBefore = .ok next := by
  rw [CoreMemDesign.edgeQuiesce]
  simp only [hp, Res.ok_bind, hc, Bool.false_eq_true, ↓reduceIte]


/-- **B3 conservativity**: on a slot whose first edge/NBA/settle pass causes
no further retained edge event, the in-slot iterator is the identity.  This is
the exact pre-B3 admitted fragment; designs with a follow-up event take the
new §4.4/§4.5 iteration path instead. -/
theorem CoreMemDesign.edgeQuiesce_eq_edgePass_of_no_followup
    {E : CoreMemDesign} {st combBefore next : CoreMemState} {before after : SvState}
    (hp : E.edgePass st before after combBefore = .ok next)
    (hc : E.processes.toList.any
      (CoreMemProc.firesIn after (E.scalar.view next.scalar)) = false) :
    E.edgeQuiesce 4096 st before after combBefore = .ok next := by
  apply CoreMemDesign.edgeQuiesce_succ_of_no_followup (n := 4095) hp hc

#print axioms CoreMemDesign.edgeQuiesce_eq_edgePass_of_no_followup

def CoreMemDesign.prepareStep (E : CoreMemDesign) (st : CoreMemState) (entry : SvState) :
    Res (CoreMemState × SvState × SvState) := do
  let inputStore := E.scalar.applyInputs st.scalar entry
  let memoryInput := E.applyMemoryInputs entry st.memory
  let inputState := E.normalizeScalar { st with memory := memoryInput } inputStore
  let pre0 ← E.settleCanonical E.env E.elems inputState E.processes.toList
  let pre ← if E.hasComb then
      E.runCombSettleQuiesce 4096 st pre0 E.processes.toList
    else .ok pre0
  let pre ← if E.hasImplicit then
      E.runImplicit st pre E.processes.toList
    else .ok pre
  let pre ← E.settleCanonical E.env E.elems pre E.processes.toList
  .ok (pre, E.scalar.view st.scalar, E.scalar.view pre.scalar)

def CoreMemDesign.stepOnePassTrace (E : CoreMemDesign) (st : CoreMemState) (entry : SvState) :
    Res (CoreMemState × Bool) := do
  let (pre, before, after) ← E.prepareStep st entry
  let next ← E.edgePass pre before after pre
  let nextView := E.scalar.view next.scalar
  let caused := E.processes.toList.any (CoreMemProc.firesIn after nextView)
  .ok (next, caused)

def CoreMemDesign.step (E : CoreMemDesign) (st : CoreMemState) (entry : SvState) : Res CoreMemState := do
  let (pre, before, after) ← E.prepareStep st entry
  E.edgeQuiesce 4096 pre before after pre

theorem CoreMemDesign.step_eq_stepOnePass_of_no_followup
    {E : CoreMemDesign} {st : CoreMemState} {entry : SvState} {next : CoreMemState}
    (h : E.stepOnePassTrace st entry = .ok (next, false)) :
    E.step st entry = .ok next := by
  unfold CoreMemDesign.stepOnePassTrace at h
  cases hp : E.prepareStep st entry with
  | timeout => simp [hp] at h
  | unsupported msg => simp [hp] at h
  | ok triple =>
      obtain ⟨pre, before, after⟩ := triple
      simp only [hp, Res.ok_bind] at h
      cases he : E.edgePass pre before after pre with
      | timeout => simp [he] at h
      | unsupported msg => simp [he] at h
      | ok pair =>
          obtain ⟨next', caused⟩ := pair
          simp only [he, Res.ok_bind, Res.ok.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, hcause⟩ := h
          simp only [CoreMemDesign.step, hp, Res.ok_bind]
          exact CoreMemDesign.edgeQuiesce_eq_edgePass_of_no_followup he hcause

#print axioms CoreMemDesign.step_eq_stepOnePass_of_no_followup


def runCoreMemRepeat (st : CoreMemState) : List SvState → Res (List CoreMemState)
  | [] => .ok []
  | _ :: rest => do
      let tail ← runCoreMemRepeat st rest
      .ok (st :: tail)

def runCoreMemRows (E : CoreMemDesign) (st : CoreMemState) : List SvState → Res (List CoreMemState)
  | [] => .ok []
  | row :: rest => do
      let st' ← E.step st row
      let tail ← if row.isEmpty && E.scalarAssignInputsOnly then
          runCoreMemRepeat st' rest
        else runCoreMemRows E st' rest
      .ok (st' :: tail)

def CoreMemState.view (E : CoreMemDesign) (st : CoreMemState) : SvState := E.scalar.view st.scalar

/-! ## Kernel smoke checks -/

private def smokeShape : MemShape :=
  { name := "s", elemWidth := 4, msb := 0, lsb := 2, id := { decl := 0 } }

private def smokeDecl : PDecl :=
  { name := "s", type := .packed [⟨.binary (.m0 .sub) (.paramRef "W" none) (.int 1), .int 0⟩] none,
    unpackedDims := [⟨.int 0, .binary (.m0 .sub) (.paramRef "P" none) (.int 1)⟩] }

#guard (smokeDecl.memShapeWithId? { vals := [("W", 4), ("P", 3)] } { decl := 0 }).toOption ==
  some smokeShape

/-! The audit's W1 refusal fixture (mclock-audit/audit_tb/t01_nba_glitch):
`p <= 1; if (c) p <= 0;` is followed by an edge process clocked by `p`.
The helper must identify `p` before elaboration can retain a canonical E
design. -/
private def auditW1Processes : List PProcess :=
  [.alwaysFF "clk"
      (.block [
        .nbaAssign "p" (.lit (.ofNat 1 1)),
        .ifStmt (.ident "c") (.nbaAssign "p" (.lit (.ofNat 1 0))) none]),
   .alwaysFF "p" (.nbaAssign "seen" (.lit (.ofNat 1 1)))]

#guard coreMemFirstRepeatedEventSource
    (coreMemEventSources auditW1Processes) auditW1Processes == some "p"

private def auditW2Processes : List PProcess :=
  [.alwaysPlain "clk"
      (.block [
        .blockingAssign "g" (.lit (.ofNat 1 1)),
        .blockingAssign "g" (.lit (.ofNat 1 0))]),
   .alwaysPlain "g" (.nbaAssign "seen" (.lit (.ofNat 1 1)))]

#guard coreMemFirstRepeatedEventSource
    (coreMemEventSources auditW2Processes) auditW2Processes == some "g"
#guard coreMemSourceHasBlockingWrite "g" auditW2Processes

private def auditW3Processes : List PProcess :=
  [.alwaysComb (.blockingAssign "a" (.ident "b")),
   .alwaysComb (.blockingAssign "b" (.ident "x"))]

#guard coreMemReactiveDependencyViol auditW3Processes == some "b"
#guard (coreMemCombDependencyViol
    { name := "auditW3", params := [], localParams := [], enums := [], decls := [],
      processes := auditW3Processes, generates := [] } []).isSome

private def auditW3bProcesses : List PProcess :=
  [.alwaysComb (.blockingAssign "t" (.ident "q")),
   .assign "t2" (.ident "t"),
   .alwaysImplicit (.blockingAssign "y" (.ident "t2"))]

#guard coreMemReactiveWrites auditW3bProcesses.head! == ["t"]
#guard coreMemReactiveReads auditW3bProcesses[2]! == ["t2"]
#guard coreMemSignalNames (.ident "t") == ["t"]
#guard coreMemAssignReactiveChainViol auditW3bProcesses == some "t2"

private def auditW3cProcesses : List PProcess :=
  [.alwaysComb (.blockingAssign "t" (.ident "q")),
   .assign "t2" (.ident "t"),
   .alwaysComb (.blockingAssign "y" (.ident "t2"))]

#guard coreMemAssignReactiveChainViol auditW3cProcesses == none

private def auditW4Processes : List PProcess :=
  [.assignL (.arrayElem "m4" [.int 0]) (.arrayElem "m3" [.int 0]),
   .assignL (.arrayElem "m3" [.int 0]) (.arrayElem "m2" [.int 0]),
   .assignL (.arrayElem "m2" [.int 0]) (.arrayElem "m1" [.int 0]),
   .assignL (.arrayElem "m1" [.int 0]) (.ident "x")]

#guard coreMemPAssignMemoryTopoB auditW4Processes == false

private def aggregateSmokeDecl : PDecl :=
  { name := "source", type := .unrecoverable none, isInput := true,
    aggregate? := some (.struct [
      ("words", .array (.int 0) (.int 1) (.struct [
        ("value", .scalar (.packed [⟨.int 3, .int 0⟩] none) false false)]))]) }

private def aggregateSmokeDesign : PDesign :=
  { name := "aggregate_smoke", params := [], localParams := [], enums := [],
    decls := [aggregateSmokeDecl,
      { name := "y", type := .packed [⟨.int 3, .int 0⟩] none, isOutput := true }],
    processes := [.alwaysComb (.blockingAssign "y"
      (.aggregateMember "source"
        [(some "words", none), (none, some (.int 0)), (some "value", none)]))],
    generates := [] }

#guard LeanModels.Sv.PExpr.hasAggregateMember
    (.aggregateMember "source" [(some "words", none), (none, some (.int 0))])
#guard LeanModels.Sv.PExpr.hasAggregateMember
    (.binary (.m0 .add) (.ident "x") (.aggregateMember "source" []))

#guard match PDesign.instantiateCoreMem aggregateSmokeDesign [] with
  | .ok E => match E.initialState with
    | .ok st => match E.evalExpr E.env E.elems st none
        (.aggregateMember "source"
          [(some "words", none), (none, some (.int 0)), (some "value", none)]) with
      | .ok value => value.toBinString == "xxxx"
      | _ => false
    | _ => false
  | _ => false

private def auditW5Processes : List PProcess :=
  [.alwaysComb (.blockingAssign "g" (.unary (.m0 .bnot) (.ident "k"))),
   .alwaysFF "g" (.nbaAssign "seen" (.lit (.ofNat 1 1)))]

#guard coreMemFirstTimeZeroEventSource
    (coreMemEventSources auditW5Processes) auditW5Processes == some "g"
#guard (coreMemTimeZeroEventSourceViol
    { name := "auditW5", params := [], localParams := [], enums := [], decls := [],
      processes := auditW5Processes, generates := [] } []).isSome

end LeanModels.Sv.Kernel

#print axioms LeanModels.Sv.Kernel.CoreMemDesign.step
