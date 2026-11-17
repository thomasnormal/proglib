import LeanModels.Sv.Kernel.Core1Elab
import LeanModels.Sv.Kernel.MemElab
import LeanModels.Sv.Loop2

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

inductive CoreMemProc where
  | edge (p : CoreMemEdge)
  | assign (target : PLhs) (value : PExpr)
  | initial (body : PStmt)
  /-- An `always_comb` body runs once at time zero and is reactivated when a
      value in its implicit sensitivity set changes.  The retained `PStmt`
      stays source-shaped; this route does not lower it to `Process2`. -/
  | comb (body : PStmt)
  /-- A plain `always @*` waits for a raw read change before activation.
      Its source body remains a `PStmt`; the memory route does not lower it
      into a clocked or combinational surrogate. -/
  | implicit (body : PStmt)
  /-- A level-sensitive `always_latch`; its source node uses the exact
      implicit-sensitivity executor while remaining distinct in the AST. -/
  | latch (body : PStmt)
  | unsupported (kind text : String)
deriving Repr, Inhabited

structure CoreMemDesign where
  name : String
  env : IEnv
  /-- Element widths for the retained source declarations.  `instExpr2`
      needs this table to lower a packed bit select; keeping it beside the
      source-shaped design avoids manufacturing a second declaration view. -/
  elems : List (String × Nat)
  scalar : Elab
  scalarEdge : Elab1
  memories : Array CoreMemDecl
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
deriving Inhabited

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

theorem CoreMemDesign.compactScalar_of_view_eq
    (E : CoreMemDesign) (st : CoreMemState) (view : SvState)
    (h : E.scalar.view st.scalar = view) :
    E.compactScalar st view = st := by
  simp [CoreMemDesign.compactScalar, h]

def CoreMemDesign.initial (E : CoreMemDesign) : CoreMemState :=
  let cache := E.scalarCacheOf E.scalar.initStore
  { scalar := E.scalarStore cache
    scalarCache := cache
    memory := MemState.ofShapes (E.memories.toList.map CoreMemDecl.shape) }

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
  if !pd.unpackedDims.isEmpty then
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
            | _ => .unsupported s!"decl '{pd.name}': non-literal initializer outside E"

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

def buildMemDecls1 (env : IEnv) : List PDecl → Nat → Res (List CoreMemDecl)
  | [], _ => .ok []
  | pd :: rest, ordinal => do
      let tail ← buildMemDecls1 env rest (ordinal + 1)
      match pd.memShapeWithId? env ({ decl := ordinal } : MemId) with
      | .error e => .unsupported e
      | .ok none => .ok tail
      | .ok (some shape) => .ok ({ source := pd, shape } :: tail)

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
  | .alwaysFFR _ _ body _ | .initial body => coreMemStmtWrites body
  | .assign _ _ | .assignL _ _ | .unsupported _ _ => []

def coreMemProcBlockingWrites : PProcess → List String
  | .alwaysFF _ body | .alwaysFFNegedge _ body | .alwaysPlain _ body
  | .alwaysComb body | .alwaysLatch body | .alwaysImplicit body
  | .alwaysFFR _ _ body _ | .initial body => coreMemStmtBlockingWrites body
  | .assign _ _ | .assignL _ _ | .unsupported _ _ => []

def coreMemEventSources : List PProcess → List String
  | [] => []
  | .alwaysFF clock _ :: rest => clock :: coreMemEventSources rest
  | .alwaysFFNegedge clock _ :: rest => clock :: coreMemEventSources rest
  | .alwaysPlain clock _ :: rest => clock :: coreMemEventSources rest
  | .alwaysFFR clock reset _ _ :: rest =>
      clock :: reset :: coreMemEventSources rest
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

def coreMemSourceWrittenAtTimeZero (name : String) : List PProcess → Bool
  | [] => false
  | p :: rest =>
      (coreMemTimeZeroProcWrites p).contains name ||
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
          s!"9.2.2.2/9.6: event source '{source}' is driven by an initial/always_comb/always_latch activation at time zero; canonical E requires the settled start state")
      else none
  | none =>
      match coreMemFirstTimeZeroEventSource (coreMemEventSources processes) processes with
      | none => none
      | some source =>
          some ("Event:time-zero",
            s!"9.2.2.2/9.6: event source '{source}' is driven by an initial/always_comb/always_latch activation at time zero; canonical E requires the settled start state")

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
  match md.driverRecords with
  | [r] =>
      r.bounds == (0, Int.ofNat md.width - 1) &&
        r.ownerKind == "ContinuousAssignSymbol" && r.generated && r.source == md.name &&
        generated.any (fun p => match p with
          | .assign target _ => target == md.name
          | .assignL (.ident target) _ => target == md.name
          | _ => false)
  | _ => false

def coreMemNetAllowed (d : PDesign) (generated : List PProcess) (kind name : String) : Bool :=
  d.others.any (fun entry => entry.1 == kind && entry.2 == name) &&
    d.netMetadata.any (fun md => md.name == name &&
      (coreMemNetMetadataAllowed md || coreMemNetDriverAllowed md generated))

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
    if coreMemNetMetadataAllowed md || coreMemNetDriverAllowed md generated then
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

def coreMemSubstExpr (vals : List (String × Int)) : PExpr → PExpr
  | .genvarRef n =>
      match vals.lookup n with
      | some v => .int v
      | none => .genvarRef n
  | .unary op a => .unary op (coreMemSubstExpr vals a)
  | .binary op a b => .binary op (coreMemSubstExpr vals a) (coreMemSubstExpr vals b)
  | .ternary c a b => .ternary (coreMemSubstExpr vals c) (coreMemSubstExpr vals a)
      (coreMemSubstExpr vals b)
  | .concat xs => .concat (xs.map (coreMemSubstExpr vals))
  | .resize w a => .resize w (coreMemSubstExpr vals a)
  | .signedResize w a => .signedResize w (coreMemSubstExpr vals a)
  | .squash2 w a => .squash2 w (coreMemSubstExpr vals a)
  | .sysCall fn a => .sysCall fn (coreMemSubstExpr vals a)
  | .bitSel a b => .bitSel (coreMemSubstExpr vals a) (coreMemSubstExpr vals b)
  | .partSel a b c => .partSel (coreMemSubstExpr vals a) (coreMemSubstExpr vals b)
      (coreMemSubstExpr vals c)
  | .repl a b => .repl (coreMemSubstExpr vals a) (coreMemSubstExpr vals b)
  | .reduce op a => .reduce op (coreMemSubstExpr vals a)
  | .cast s a => .cast s (coreMemSubstExpr vals a)
  | .arrayElem n xs => .arrayElem n (xs.map (coreMemSubstExpr vals))
  | .arrayPart n xs mode a b => .arrayPart n (xs.map (coreMemSubstExpr vals)) mode
      (coreMemSubstExpr vals a) (coreMemSubstExpr vals b)
  | .functionCall n xs => .functionCall n (xs.map (coreMemSubstExpr vals))
  | e => e

def coreMemSubstLhs (vals : List (String × Int)) : PLhs → PLhs
  | .bitSel n i => .bitSel n (coreMemSubstExpr vals i)
  | .partSel n a b => .partSel n (coreMemSubstExpr vals a) (coreMemSubstExpr vals b)
  | .concat xs => .concat (xs.map (coreMemSubstLhs vals))
  | .arrayElem n xs => .arrayElem n (xs.map (coreMemSubstExpr vals))
  | .arrayPart n xs mode a b => .arrayPart n (xs.map (coreMemSubstExpr vals)) mode
      (coreMemSubstExpr vals a) (coreMemSubstExpr vals b)
  | l => l

def coreMemSubstDim (vals : List (String × Int)) (d : PDim) : PDim :=
  { msb := coreMemSubstExpr vals d.msb, lsb := coreMemSubstExpr vals d.lsb }

def coreMemSubstType (vals : List (String × Int)) : PType → PType
  | .packed dims resolved => .packed (dims.map (coreMemSubstDim vals)) resolved
  | .typeRef n pkg resolved => .typeRef n pkg resolved
  | .unrecoverable resolved => .unrecoverable resolved

def coreMemSubstDecl (vals : List (String × Int)) (d : PDecl) : PDecl :=
  { name := d.name, type := coreMemSubstType vals d.type,
    unpackedDims := d.unpackedDims.map (coreMemSubstDim vals),
    isSigned := d.isSigned, twoState := d.twoState, isInput := d.isInput,
    isOutput := d.isOutput, isNet := d.isNet,
    init := d.init.map (coreMemSubstExpr vals), flatBase := d.flatBase,
    flatIndex := d.flatIndex }

mutual
def coreMemSubstStmt (vals : List (String × Int)) : PStmt → PStmt
  | .blockingAssign n e => .blockingAssign n (coreMemSubstExpr vals e)
  | .nbaAssign n e => .nbaAssign n (coreMemSubstExpr vals e)
  | .ifStmt c t e => .ifStmt (coreMemSubstExpr vals c) (coreMemSubstStmt vals t)
      (coreMemSubstStmtOpt vals e)
  | .block xs => .block (coreMemSubstStmtList vals xs)
  | .forLoop n i c s b => .forLoop n (coreMemSubstExpr vals i)
      (coreMemSubstExpr vals c) (coreMemSubstExpr vals s) (coreMemSubstStmt vals b)
  | .blockingAssignL l e => .blockingAssignL (coreMemSubstLhs vals l)
      (coreMemSubstExpr vals e)
  | .nbaAssignL l e => .nbaAssignL (coreMemSubstLhs vals l)
      (coreMemSubstExpr vals e)
  | .caseStmt s items d mode check =>
      .caseStmt (coreMemSubstExpr vals s)
        (coreMemSubstCaseItems vals items) (coreMemSubstStmtOpt vals d) mode check
  | s => s
termination_by structural s => s

def coreMemSubstStmtOpt (vals : List (String × Int)) : Option PStmt → Option PStmt
  | none => none
  | some s => some (coreMemSubstStmt vals s)
termination_by structural o => o

def coreMemSubstStmtList (vals : List (String × Int)) : List PStmt → List PStmt
  | [] => []
  | s :: ss => coreMemSubstStmt vals s :: coreMemSubstStmtList vals ss
termination_by structural xs => xs

def coreMemSubstCaseItems (vals : List (String × Int)) :
    List (List PExpr × PStmt) → List (List PExpr × PStmt)
  | [] => []
  | (ps, b) :: rest =>
      (ps.map (coreMemSubstExpr vals), coreMemSubstStmt vals b) ::
        coreMemSubstCaseItems vals rest
termination_by structural xs => xs

def coreMemSubstProcess (vals : List (String × Int)) : PProcess → PProcess
  | .alwaysFF c b => .alwaysFF c (coreMemSubstStmt vals b)
  | .alwaysFFNegedge c b => .alwaysFFNegedge c (coreMemSubstStmt vals b)
  | .alwaysPlain c b => .alwaysPlain c (coreMemSubstStmt vals b)
  | .alwaysComb b => .alwaysComb (coreMemSubstStmt vals b)
  | .alwaysLatch b => .alwaysLatch (coreMemSubstStmt vals b)
  | .alwaysImplicit b => .alwaysImplicit (coreMemSubstStmt vals b)
  | .assign n e => .assign n (coreMemSubstExpr vals e)
  | .assignL l e => .assignL (coreMemSubstLhs vals l) (coreMemSubstExpr vals e)
  | .alwaysFFR c r b h => .alwaysFFR c r (coreMemSubstStmt vals b) h
  | .initial b => .initial (coreMemSubstStmt vals b)
  | p => p
end

def coreMemBindVals (env : IEnv) (vals : List (String × Int)) : IEnv :=
  -- `vals` is ordered from the innermost generate scope outward. Binding the
  -- reverse list preserves the head-first shadowing used by `lookup`.
  vals.reverse.foldl (fun e (n, v) => e.bindVal n v) env

/-! Active generated declarations are collected from the same source-shaped
walk as generated processes.  A declaration is copied once for each active
generate instance, with genvar references substituted in its dimensions;
inactive branches are never visited.  This is the declaration half of IEEE
1800-2023 §§27.4/27.5 and deliberately does not lower a declaration to cells.
-/

mutual
def coreMemGeneratedDeclsItem (env : IEnv) (iterFuel : Nat)
    (vals : List (String × Int)) : GenItem → Res (List PDecl)
  | .process _ | .unsupported _ _ | .inst _ => .ok []
  | .decl d => .ok [coreMemSubstDecl vals d]
  | .genIf cond thenB elseB =>
      match evalGenGuard (coreMemBindVals env vals) cond with
      | .error e => .unsupported s!"generate if: {e}"
      | .ok v => if v != 0 then coreMemGeneratedDeclsList env iterFuel vals thenB
                 else coreMemGeneratedDeclsList env iterFuel vals elseB
  | .genFor _label g initE bound step _rc body =>
      let env' := coreMemBindVals env vals
      match evalInt env' initE, stepDelta g step with
      | .ok i0, .ok δ => do
          let vs ← genvarSeq env' g bound δ iterFuel i0
          coreMemGeneratedDeclsIters env iterFuel vals g vs body
      | .error e, _ => .unsupported s!"generate for: {e}"
      | _, .error e => .unsupported s!"generate for: {e}"
  termination_by it => (sizeOf it, 0)
  decreasing_by all_goals (simp_wf; omega)

def coreMemGeneratedDeclsList (env : IEnv) (iterFuel : Nat)
    (vals : List (String × Int)) : List GenItem → Res (List PDecl)
  | [] => .ok []
  | it :: rest => do
      let ds ← coreMemGeneratedDeclsItem env iterFuel vals it
      let tail ← coreMemGeneratedDeclsList env iterFuel vals rest
      .ok (ds ++ tail)
  termination_by xs => (sizeOf xs, 0)
  decreasing_by all_goals (simp_wf; omega)

def coreMemGeneratedDeclsIters (env : IEnv) (iterFuel : Nat)
    (vals : List (String × Int)) (g : String) : List Int → List GenItem → Res (List PDecl)
  | [], _ => .ok []
  | v :: vs, body => do
      let ds ← coreMemGeneratedDeclsList env iterFuel ((g, v) :: vals) body
      let tail ← coreMemGeneratedDeclsIters env iterFuel vals g vs body
      .ok (ds ++ tail)
  termination_by vs body => (sizeOf body, vs.length + 1)
  decreasing_by all_goals (simp_wf; omega)
end

def coreMemDeclNamesUnique (decls : List PDecl) : Bool :=
  let names := decls.map (fun d => d.name)
  names.eraseDups.length == names.length

mutual
def coreMemExpandItem (env : IEnv) (iterFuel : Nat) (vals : List (String × Int)) :
    GenItem → Res (List PProcess)
  | .process p => .ok [coreMemSubstProcess vals p]
  | .decl _ => .ok []
  | .unsupported k t => .ok [.unsupported k t]
  | .inst i => .ok [.unsupported "Instance"
      s!"module instance '{i.name}' of '{i.module}' outside the canonical E memory route"]
  | .genIf cond thenB elseB =>
      match evalGenGuard (coreMemBindVals env vals) cond with
      | .error e => .unsupported s!"generate if: {e}"
      | .ok v => if v != 0 then coreMemExpandList env iterFuel vals thenB
                 else coreMemExpandList env iterFuel vals elseB
  | .genFor _label g initE bound step _rc body =>
      let env' := coreMemBindVals env vals
      match evalInt env' initE, stepDelta g step with
      | .ok i0, .ok δ => do
          let vs ← genvarSeq env' g bound δ iterFuel i0
          coreMemExpandIters env iterFuel vals g vs body
      | .error e, _ => .unsupported s!"generate for: {e}"
      | _, .error e => .unsupported s!"generate for: {e}"
  termination_by it => (sizeOf it, 0)
  decreasing_by all_goals (simp_wf; omega)

def coreMemExpandList (env : IEnv) (iterFuel : Nat) (vals : List (String × Int)) :
    List GenItem → Res (List PProcess)
  | [] => .ok []
  | it :: rest => do
      let ps ← coreMemExpandItem env iterFuel vals it
      let qs ← coreMemExpandList env iterFuel vals rest
      .ok (ps ++ qs)
  termination_by xs => (sizeOf xs, 0)
  decreasing_by all_goals (simp_wf; omega)

def coreMemExpandIters (env : IEnv) (iterFuel : Nat) (vals : List (String × Int))
    (g : String) : List Int → List GenItem → Res (List PProcess)
  | [], _ => .ok []
  | v :: vs, body => do
      let ps ← coreMemExpandList env iterFuel ((g, v) :: vals) body
      let qs ← coreMemExpandIters env iterFuel vals g vs body
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
  | .lit _ | .paramRef _ _ | .genvarRef _ | .enumRef _ _ _ | .int _ | .fill _
  | .unsupported _ _ => []

def coreMemSignalNamesList : List PExpr → List String
  | [] => []
  | x :: xs => coreMemSignalNames x ++ coreMemSignalNamesList xs
end

def coreMemLhsTargets : PLhs → List String
  | .ident n | .bitSel n _ | .partSel n _ _ | .arrayElem n _ | .arrayPart n .. => [n]
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
  | .unary _ a | .resize _ a | .signedResize _ a | .squash2 _ a
  | .sysCall _ a | .reduce _ a | .cast _ a => coreMemPExprHasMemory a
  | .binary _ a b => coreMemPExprHasMemory a || coreMemPExprHasMemory b
  | .ternary c a b => coreMemPExprHasMemory c || coreMemPExprHasMemory a || coreMemPExprHasMemory b
  | .concat xs | .functionCall _ xs => coreMemPExprHasMemoryList xs
  | .bitSel a b | .repl a b => coreMemPExprHasMemory a || coreMemPExprHasMemory b
  | .partSel a b c => coreMemPExprHasMemory a || coreMemPExprHasMemory b || coreMemPExprHasMemory c
  | .lit _ | .ident _ | .paramRef .. | .genvarRef _ | .enumRef .. | .int _
  | .fill _ | .unsupported .. => false

def coreMemPExprHasMemoryList : List PExpr → Bool
  | [] => false
  | x :: xs => coreMemPExprHasMemory x || coreMemPExprHasMemoryList xs

end

mutual
def coreMemPLhsHasMemory : PLhs → Bool
  | .arrayElem .. | .arrayPart .. => true
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

def coreMemLhsReadNamesList : List PLhs → List String
  | [] => []
  | lhs :: rest => coreMemLhsReadNames lhs ++ coreMemLhsReadNamesList rest

end

def coreMemReactiveProc : PProcess → Bool
  | .alwaysComb _ | .alwaysLatch _ | .alwaysImplicit _ => true
  | _ => false

def coreMemReactiveWrites : PProcess → List String
  | .alwaysComb body | .alwaysLatch body | .alwaysImplicit body => coreMemStmtWrites body
  | _ => []

def coreMemReactiveReads : PProcess → List String
  | .alwaysComb body | .alwaysLatch body | .alwaysImplicit body => coreMemStmtReadNames body
  | _ => []

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
        match coreMemFirstReadIn (coreMemReactiveReads p) targets with
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
              coreMemReactiveProc q &&
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
              coreMemReactiveProc q &&
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
    let envP ← bindPackageParams envI d.packageParams
    let envP ← bindPackageEnums envP d.enums
    let env0 ← bindParamsRes envP d.params args
    let env1 ← bindLocals env0 d.localParams
    let env2 ← bindEnums env1 d.enums
    let pws ← typedParamWidthsE env2
      (d.params.map (fun p => (p.name, p.type?))
        ++ d.localParams.map (fun lp => (lp.name, lp.type?)))
    let env2 := { env2 with pwidths := pws }
    let env2 := { env2 with dims := dimTable env2 d.decls }
    let env2 := { env2 with functions := d.functions }
    let generatedDecls ← coreMemGeneratedDeclsList env2 iterFuel [] d.generates
    let sourceNames := (d.decls ++ generatedDecls).map (·.name)
    let metadataForSource := d.netMetadata.filter (fun md => !md.generated)
    let sourceDecls := d.decls ++ generatedDecls ++ coreMemMetadataDecls metadataForSource
    if !coreMemDeclNamesUnique sourceDecls then
      .unsupported "UnpackedDecl:generate-scope: active generate declarations contain duplicate names"
    else
      let env2 := { env2 with dims := dimTable env2 (d.decls ++ generatedDecls) }
      let generatedRaw ← coreMemExpandList env2 iterFuel [] d.generates
      let generated := coreMemDropGeneratedNetMarkers d generatedRaw
      let generatedMetadataOk := d.netMetadata.all (fun md =>
        !md.generated || !sourceNames.contains md.name ||
          coreMemNetMetadataAllowed md || coreMemNetDriverAllowed md generatedRaw)
      if !generatedMetadataOk then
        .unsupported "NetSymbol:net-z:generate: generated net metadata does not prove a supported §6.6 net shape"
      else match coreMemEventSourceMultiWriteViol d generated with
      | some (kind, msg) => .unsupported s!"{kind}: {msg}"
      | none =>
          match coreMemTimeZeroEventSourceViol d generated with
          | some (kind, msg) => .unsupported s!"{kind}: {msg}"
          | none =>
            let allProcesses := d.processes ++ generated
            if coreMemHasEdgeProc allProcesses && !coreMemPAssignMemoryTopoB allProcesses then
            .unsupported "Comb:memory-topology: 10.3/4.5: continuous assignment reads a memory cell driven by itself or a later assignment; canonical E requires topological source order"
            else match coreMemCombDependencyViol d generated with
          | some (kind, msg) => .unsupported s!"{kind}: {msg}"
          | none =>
            match coreMemClockResetViol d generated with
            | some (kind, msg) => .unsupported s!"{kind}: {msg}"
            | none =>
              match coreMemFirstUnsupportedOther d generated d.others with
          | some (kind, text) =>
              .unsupported s!"E memory route does not yet admit module member '{kind}' ({text})"
          | none =>
              let decls0 ← buildScalarDecls1 env2 (d.decls ++ generatedDecls)
              let decls := decls0 ++ (coreMemNetDecls d generated).filter
                (fun dc => !sourceNames.contains dc.name)
              let elems ← buildElems env2 sourceDecls
              let envP := { env2 with widths := decls.map (fun dc => (dc.name, dc.width)) }
              let memories ← buildMemDecls1 envP (d.decls ++ generatedDecls) 0
              if memories.isEmpty && (d.decls ++ generatedDecls).any (fun pd => !pd.unpackedDims.isEmpty) then
                .unsupported "UnpackedDecl:memory: no one-rank unpacked declaration was admitted"
              else
                let scalar : Elab :=
                  { name := d.name, decls := decls.toArray, procs := #[] }
                let scalarEdge : Elab1 :=
                  { decls := decls.toArray, procs := #[], name := d.name }
                let processes := (d.processes.map (CoreMemProc.ofPProcessAt envP)) ++
                  (generated.map (CoreMemProc.ofPProcessAt envP))
                let result : CoreMemDesign :=
                    { name := d.name, env := envP, elems, scalar := scalar, scalarEdge := scalarEdge,
                      memories := memories.toArray, processes := processes.toArray,
                      readmemh := d.readmemh }
                .ok { result with compiledAssigns := result.compileAssigns }

/-! ## Expressions -/

mutual

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
  | .lit _ | .ident _ | .paramRef .. | .genvarRef _ | .enumRef .. | .int _
  | .fill _ | .unsupported .. => false

def LeanModels.Sv.PExpr.hasMemoryReadList : List PExpr → Bool
  | [] => false
  | x :: xs => LeanModels.Sv.PExpr.hasMemoryRead x ||
      LeanModels.Sv.PExpr.hasMemoryReadList xs

def LeanModels.Sv.PExpr.hasFunctionCall : PExpr → Bool
  | .functionCall _ _ => true
  | .unary _ a | .resize _ a | .signedResize _ a | .squash2 _ a
  | .sysCall _ a | .reduce _ a | .cast _ a => LeanModels.Sv.PExpr.hasFunctionCall a
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
  | .lit _ | .ident _ | .paramRef .. | .genvarRef _ | .enumRef .. | .int _
  | .fill _ | .unsupported .. => false

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

def coreMemReadExprs : PExpr → List PExpr
  | e@(.ident _) => [e]
  | e@(.arrayElem _ indices) => e :: coreMemReadExprsList indices
  | e@(.arrayPart _ indices _ a b) =>
      e :: (coreMemReadExprsList indices ++ coreMemReadExprs a ++ coreMemReadExprs b)
  | .unary _ a | .resize _ a | .signedResize _ a | .squash2 _ a
  | .sysCall _ a | .reduce _ a | .cast _ a => coreMemReadExprs a
  | .binary _ a b | .bitSel a b | .repl a b =>
      coreMemReadExprs a ++ coreMemReadExprs b
  | .partSel a b c | .ternary a b c =>
      coreMemReadExprs a ++ coreMemReadExprs b ++ coreMemReadExprs c
  | .concat xs | .functionCall _ xs => coreMemReadExprsList xs
  | .lit _ | .fill _ | .paramRef .. | .genvarRef _ | .enumRef .. | .int _
  | .unsupported .. => []

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

def coreMemLhsReadExprsList : List PLhs → List PExpr
  | [] => []
  | lhs :: rest => coreMemLhsReadExprs lhs ++ coreMemLhsReadExprsList rest

def coreMemStmtReadExprs : PStmt → List PExpr
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

/-! The ordinary E entry is defined after the source-shaped sensitivity
walkers so its derived cache is built once at instantiation, never in a cycle.
The source nodes remain in `CoreMemProc`; this is an evaluator cache only. -/

def CoreMemDesign.compileCombReads (E : CoreMemDesign) :
    Array (Option (List Expr2)) :=
  E.processes.map fun p =>
    match p with
    | .comb body =>
        let reads := coreMemStmtReadExprs body
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
        let reads := coreMemStmtReadExprs body
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

mutual

def CoreMemDesign.evalIndexLocals (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (locals : SvState) (e : PExpr) : Res LVec :=
  match evalInt env e with
  | .ok i => .ok (LVec.ofInt 32 i)
  | .error _ => E.evalExprLocals env elems st none locals e

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

/-! A continuous scalar assignment has no local bindings.  Once the source
expression has no native-memory read, its `Expr2` lowering is independent of
the state and can be reused from `CoreMemDesign.compiledAssigns`; a memory
read must stay on `evalExpr`, whose source-shaped evaluator threads
`MemState`. -/
def CoreMemDesign.evalScalarAssignAtView (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) (view : SvState)
    (ctx : Option Nat) (index : Nat) (value : PExpr) : Res LVec :=
  if LeanModels.Sv.PExpr.hasMemoryRead value || LeanModels.Sv.PExpr.hasFunctionCall value then
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

def CoreMemExec.append (a b : CoreMemExecResult) : CoreMemExecResult :=
  { state := b.state, scalarQ := a.scalarQ ++ b.scalarQ, memoryQ := a.memoryQ ++ b.memoryQ }

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

def CoreMemDesign.readChanged (E : CoreMemDesign) (before after : CoreMemState)
    (reads : List PExpr) : Res Bool :=
  match reads with
  | [] => .ok false
  | expr :: rest => do
      let old ← E.evalExpr E.env E.elems before none expr
      let now ← E.evalExpr E.env E.elems after none expr
      if old == now then E.readChanged before after rest else .ok true

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
  if !LeanModels.Sv.PExpr.hasMemoryRead e && !LeanModels.Sv.PExpr.hasFunctionCall e then
    evalPure2 view (instExpr2 env elems ctx e)
  else
    E.evalExpr env elems st ctx e

mutual

def CoreMemDesign.execCombStmtFuel (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) (view : SvState) : Nat → PStmt →
    Res (CoreMemState × SvState)
  | 0, _ => .timeout
  | fuel + 1, .blockingAssign name value =>
      match E.scalarTarget name with
      | none => .unsupported s!"9.2.2.2: scalar always_comb target '{name}' is undeclared"
      | some width => do
          let v ← E.evalCombExpr env elems st view (some width) value
          let st' := E.setScalarState st name v
          .ok (st', SvState.set view name v)
  | fuel + 1, .blockingAssignL target value =>
      match target with
      | .ident name =>
          match E.scalarTarget name with
          | none => .unsupported s!"9.2.2.2: scalar always_comb target '{name}' is undeclared"
          | some width => do
              let v ← E.evalCombExpr env elems st view (some width) value
              let st' := E.setScalarState st name v
              .ok (st', SvState.set view name v)
      | .arrayElem name [_] =>
          match E.memDecl? name with
          | none => .unsupported s!"9.2.2.2: memory always_comb target '{name}' is undeclared"
          | some md => do
              let v ← E.evalExpr env elems st (some md.shape.elemWidth) value
              let st' ← E.writeInitialCell env elems st target name md v
              .ok (st', view)
      | .arrayElem name _ =>
          .unsupported s!"9.2.2.2: memory always_comb target '{name}' is not one-rank"
      | _ => .unsupported "9.2.2.2: packed or concatenated always_comb target is outside this slice"
  | fuel + 1, .ifStmt cond yes no => do
      let cv ← E.evalCombExpr env elems st view (some 1) cond
      if cv.condTrue then E.execCombStmtFuel env elems st view fuel yes
      else match no with
        | none => .ok (st, view)
        | some stmt => E.execCombStmtFuel env elems st view fuel stmt
  | fuel + 1, .block body => E.execCombStmtsFuel env elems st view fuel body
  | fuel + 1, .forLoop .. =>
      .unsupported "9.2.2.2: procedural loop in always_comb body is outside this slice"
  | fuel + 1, .caseStmt subject items default? mode check => do
      let sv ← E.evalExpr env elems st none subject
      match check with
      | .none =>
          let selected ← coreMemSelectCase E env elems st sv mode items default?
          match selected with
          | none => .ok (st, view)
          | some body => E.execCombStmtFuel env elems st view fuel body
      | qualifier =>
          let n ← coreMemCaseHits E env elems st sv mode items
          if caseClaimOk qualifier default?.isSome n then
            let selected ← coreMemSelectCase E env elems st sv mode items default?
            match selected with
            | none => .ok (st, view)
            | some body => E.execCombStmtFuel env elems st view fuel body
          else
            .unsupported s!"12.5.3: {caseCheckName qualifier}"
  | fuel + 1, .nbaAssign .. | fuel + 1, .nbaAssignL .. =>
      .unsupported "10.4.2: nonblocking assignment in always_comb body"
  | fuel + 1, .unsupported kind text => .unsupported s!"{kind}: {text}"

def CoreMemDesign.execCombStmtsFuel (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) (view : SvState) : Nat → List PStmt →
    Res (CoreMemState × SvState)
  | 0, _ => .timeout
  | fuel + 1, [] => .ok (st, view)
  | fuel + 1, stmt :: rest => do
      let (st', view') ← E.execCombStmtFuel env elems st view fuel stmt
      E.execCombStmtsFuel env elems st' view' fuel rest

end

def CoreMemDesign.execCombStmtAtView (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) (view : SvState) (stmt : PStmt) :
    Res (CoreMemState × SvState) :=
  E.execCombStmtFuel env elems st view 4096 stmt

def CoreMemDesign.execCombStmt (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) (stmt : PStmt) : Res CoreMemState :=
  do
    let (st', view') ← E.execCombStmtAtView env elems st (E.scalar.view st.scalar) stmt
    .ok (E.compactScalar st' view')


def CoreMemDesign.runImplicitAt (E : CoreMemDesign) (before current : CoreMemState)
    (beforeView currentView : SvState) (index : Nat) :
    List CoreMemProc → Res CoreMemState
  | [] => .ok current
  | .implicit body :: rest => do
      let reads := coreMemStmtReadExprs body
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
  | .assign _ _ :: rest => E.runImplicitAt before current beforeView currentView (index + 1) rest
  | .edge _ :: rest => E.runImplicitAt before current beforeView currentView (index + 1) rest
  | .initial _ :: rest => E.runImplicitAt before current beforeView currentView (index + 1) rest
  | .comb _ :: rest => E.runImplicitAt before current beforeView currentView (index + 1) rest
  | .latch _ :: rest => E.runImplicitAt before current beforeView currentView (index + 1) rest
  | .unsupported kind text :: _ => .unsupported s!"{kind}: {text}"

def CoreMemDesign.runImplicit (E : CoreMemDesign) (before current : CoreMemState) :
    List CoreMemProc → Res CoreMemState := fun procs =>
  E.runImplicitAt before current (E.scalar.view before.scalar)
    (E.scalar.view current.scalar) 0 procs

def CoreMemDesign.runCombInitialWithView (E : CoreMemDesign) (current : CoreMemState)
    (view : SvState) : List CoreMemProc → Res (CoreMemState × SvState)
  | [] => .ok (current, view)
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

def CoreMemDesign.runCombAt (E : CoreMemDesign) (before : CoreMemState)
    (beforeView : SvState) (current : CoreMemState) (currentView : SvState)
    (index : Nat) : List CoreMemProc → Res CoreMemState
  | [] => .ok current
  | .comb body :: rest => do
      let reads := coreMemStmtReadExprs body
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
  | .latch body :: rest => do
      let reads := coreMemStmtReadExprs body
      let ready ← E.readChangedAt before current beforeView currentView index reads
      if !ready then
        E.runCombAt before beforeView current currentView (index + 1) rest
      else
        let (after, afterView) ← E.execCombStmtAtView E.env E.elems current currentView body
        let after := E.compactScalar after afterView
        E.runCombAt before beforeView after afterView (index + 1) rest
  | .unsupported kind text :: _ => .unsupported s!"{kind}: {text}"

def CoreMemDesign.runComb (E : CoreMemDesign) (before current : CoreMemState) :
    List CoreMemProc → Res CoreMemState := fun procs =>
  E.runCombAt before (E.scalar.view before.scalar) current
    (E.scalar.view current.scalar) 0 procs

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

mutual

def CoreMemDesign.execStmtFuel (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) : Nat → PStmt → CoreMemExec
  | 0, _ => .timeout
  | fuel + 1, .nbaAssign target value =>
      match E.scalarTarget target with
      | none => .unsupported s!"11.5.1: scalar NBA target '{target}' is undeclared"
      | some width => do
          let v ← E.evalExpr env elems st (some width) value
          CoreMemExec.fromQueue st (E.issueTarget env elems st (.ident target) v)
  | fuel + 1, .nbaAssignL target value =>
      match target with
      | .ident name =>
          match E.scalarTarget name with
          | none => .unsupported s!"11.5.1: scalar NBA target '{name}' is undeclared"
          | some width => do
              let v ← E.evalExpr env elems st (some width) value
              CoreMemExec.fromQueue st (E.issueTarget env elems st target v)
      | .arrayElem name indices =>
          match E.memDecl? name with
          | none => do
              let (_, width) ← E.scalarLhs2 env elems target
              let v ← E.evalExpr env elems st (some width) value
              CoreMemExec.fromQueue st (E.issueScalarTarget env elems st target v)
          | some md =>
              match indices with
              | [_] => do
                  let v ← E.evalExpr env elems st (some md.shape.elemWidth) value
                  CoreMemExec.fromQueue st (E.issueTarget env elems st target v)
              | _ => .unsupported s!"11.5.1: memory target '{name}' is not one-rank"
      | target => do
          let (_, width) ← E.scalarLhs2 env elems target
          let v ← E.evalExpr env elems st (some width) value
          CoreMemExec.fromQueue st (E.issueScalarTarget env elems st target v)
  | fuel + 1, .blockingAssign name value => do
      let st' ← E.execBlockingTarget env elems st (.ident name) value
      .ok { state := st', scalarQ := [], memoryQ := [] }
  | fuel + 1, .blockingAssignL target value => do
      let st' ← E.execBlockingTarget env elems st target value
      .ok { state := st', scalarQ := [], memoryQ := [] }
  | fuel + 1, .ifStmt cond yes no => do
      let cv ← E.evalExpr env elems st (some 1) cond
      if cv.condTrue then E.execStmtFuel env elems st fuel yes
      else match no with
        | none => .ok { state := st, scalarQ := [], memoryQ := [] }
        | some s => E.execStmtFuel env elems st fuel s
  | fuel + 1, .block body => E.execStmtsFuel env elems st fuel body
  | fuel + 1, .forLoop iterator init condition step body =>
      match forValues2 env iterator init condition step with
      | .timeout => .timeout
      | .unsupported e => .unsupported s!"ForLoopStatement: {e}"
      | .ok values => E.execLoopValuesFuel env elems st fuel values body iterator
  | fuel + 1, .caseStmt subject items default? mode check => do
      let sv ← E.evalExpr env elems st none subject
      match check with
      | .none =>
          let selected ← coreMemSelectCase E env elems st sv mode items default?
          match selected with
          | none => .ok { state := st, scalarQ := [], memoryQ := [] }
          | some body => E.execStmtFuel env elems st fuel body
      | qualifier =>
          let n ← coreMemCaseHits E env elems st sv mode items
          if caseClaimOk qualifier default?.isSome n then
            let selected ← coreMemSelectCase E env elems st sv mode items default?
            match selected with
            | none => .ok { state := st, scalarQ := [], memoryQ := [] }
            | some body => E.execStmtFuel env elems st fuel body
          else
            .unsupported s!"12.5.3: {caseCheckName qualifier}"
  | fuel + 1, .unsupported kind text => .unsupported s!"{kind}: {text}"

def CoreMemDesign.execStmtsFuel (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) : Nat → List PStmt → CoreMemExec
  | 0, _ => .timeout
  | fuel + 1, [] => .ok { state := st, scalarQ := [], memoryQ := [] }
  | fuel + 1, stmt :: rest => do
      let a ← E.execStmtFuel env elems st fuel stmt
      let b ← E.execStmtsFuel env elems a.state fuel rest
      .ok (CoreMemExec.append a b)

def CoreMemDesign.execLoopValuesFuel (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) : Nat → List Int → PStmt → String → CoreMemExec
  | 0, _, _, _ => .timeout
  | fuel + 1, [], _, _ => .ok { state := st, scalarQ := [], memoryQ := [] }
  | fuel + 1, i :: rest, body, iterator => do
      let a ← E.execStmtFuel (env.bindVal iterator i) elems st fuel body
      let b ← E.execLoopValuesFuel env elems a.state fuel rest body iterator
      .ok (CoreMemExec.append a b)

end

def CoreMemDesign.execStmt (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (stmt : PStmt) : CoreMemExec :=
  E.execStmtFuel env elems st 4096 stmt

def CoreMemDesign.execStmts (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (stmts : List PStmt) : CoreMemExec :=
  E.execStmtsFuel env elems st 4096 stmts

def CoreMemDesign.execLoopValues (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (values : List Int) (body : PStmt) (iterator : String) : CoreMemExec :=
  E.execLoopValuesFuel env elems st 4096 values body iterator

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

def CoreMemDesign.settleAssignAt (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (view : SvState) (index : Nat) : List CoreMemProc →
    Res (CoreMemState × SvState)
  | [] => .ok (st, view)
  | .assign target value :: rest => do
      match target with
      | .ident name =>
          let width ← match E.scalarWidth? name with
            | some w => .ok w
            | none => .unsupported s!"10.3: continuous target '{name}' is undeclared"
          let v ← E.evalScalarAssignAtView env elems st view (some width) index value
          let st' := E.setScalarState st name v
          E.settleAssignAt env elems st' (SvState.set view name v) (index + 1) rest
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
  | .latch _ :: rest => E.settleAssignAt env elems st view (index + 1) rest
  | .unsupported kind text :: _ =>
      .unsupported s!"{kind}: {text}"

def CoreMemDesign.settleAssign (E : CoreMemDesign) (env : IEnv) (elems : List (String × Nat))
    (st : CoreMemState) (procs : List CoreMemProc) : Res CoreMemState :=
  do
    let (st', view') ← E.settleAssignAt env elems st (E.scalar.view st.scalar) 0 procs
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

def CoreMemDesign.settleAssignWithView (E : CoreMemDesign) (env : IEnv)
    (elems : List (String × Nat)) (st : CoreMemState) (view : SvState)
    (procs : List CoreMemProc) :
    Res (CoreMemState × SvState) :=
  do
    let (st', view') ← E.settleAssignAt env elems st view 0 procs
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

def CoreMemDesign.initialState (E : CoreMemDesign) : Res CoreMemState := do
  let bodies := E.processes.toList.filterMap fun p =>
    match p with
    | .initial body => some body
    | _ => none
  let base ← if !E.readmemh.isEmpty then
    match bodies with
    | [_] => E.writeReadmemhList E.initial E.readmemh
    | [] => .unsupported "SystemTask:readmemh metadata has no initial process"
    | _ => .unsupported "SystemTask:readmemh: multiple initial processes are outside this cycle entry"
  else match bodies with
    | [] => .ok E.initial
    | [body] => E.execInitialStmt E.env E.elems E.initial 4096 body
    | _ => .unsupported "T2:Initial: multiple initial processes are outside this cycle entry"
  if !E.hasComb then
    .ok base
  else
    let (settled, settledView) ←
      E.settleAssignWithView E.env E.elems base (E.scalar.view base.scalar) E.processes.toList
    let (combed, combedView) ←
      E.runCombInitialWithView settled settledView E.processes.toList
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
      E.runComb combBefore activated E.processes.toList
    else .ok activated
  E.settleCanonical E.env E.elems combed E.processes.toList

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
      let caused := E.processes.toList.any fun p =>
        match p with
        | .edge q => q.fires after nextView
        | _ => false
      if caused then E.edgeQuiesce n next after nextView next
      else .ok next

theorem CoreMemDesign.edgeQuiesce_succ_of_no_followup
    {E : CoreMemDesign} {n : Nat} {st next combBefore : CoreMemState} {before after : SvState}
    (hp : E.edgePass st before after combBefore = .ok next)
    (hc : (E.processes.toList.any (fun p =>
      match p with
      | .edge q => q.fires after (E.scalar.view next.scalar)
      | _ => false)) = false) :
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
    (hc : (E.processes.toList.any (fun p =>
      match p with
      | .edge q => q.fires after (E.scalar.view next.scalar)
      | _ => false)) = false) :
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
      E.runComb st pre0 E.processes.toList
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
  let caused := E.processes.toList.any fun p =>
    match p with
    | .edge q => q.fires after nextView
    | _ => false
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

private def auditW4Processes : List PProcess :=
  [.assignL (.arrayElem "m4" [.int 0]) (.arrayElem "m3" [.int 0]),
   .assignL (.arrayElem "m3" [.int 0]) (.arrayElem "m2" [.int 0]),
   .assignL (.arrayElem "m2" [.int 0]) (.arrayElem "m1" [.int 0]),
   .assignL (.arrayElem "m1" [.int 0]) (.ident "x")]

#guard coreMemPAssignMemoryTopoB auditW4Processes == false

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
