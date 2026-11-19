import LeanModels.Sv.Kernel.CoreMemExec
import LeanModels.Sv.Hier2

/-!
# One source-shaped memory hierarchy in canonical E

Module elaboration follows the parser's `PDesign`/`PInst` nodes and the
IEEE 1800-2023 §23.3.3 port-connection rule. A one-child source-shaped
hierarchy is merged into one `CoreMemDesign` while retaining declaration
identities, unpacked dimensions, loop bodies, and NBA timing. The executor is
the existing canonical `MemState`/`MemNbaQueue` route; no MemE adapter,
Design2 lowering, cell expansion, or second memory store is introduced.
-/
namespace LeanModels.Sv.Kernel
open LeanModels.Sv
set_option autoImplicit false

mutual
private def hExpr (pfx : String) : PExpr → PExpr
  | .ident n => .ident (pfx ++ n)
  | .arrayElem n is => .arrayElem (pfx ++ n) (is.map (hExpr pfx))
  | .arrayPart n is m a b => .arrayPart (pfx ++ n) (is.map (hExpr pfx)) m (hExpr pfx a) (hExpr pfx b)
  | .bitSel a b => .bitSel (hExpr pfx a) (hExpr pfx b)
  | .partSel a b c => .partSel (hExpr pfx a) (hExpr pfx b) (hExpr pfx c)
  | .unary o a => .unary o (hExpr pfx a)
  | .binary o a b => .binary o (hExpr pfx a) (hExpr pfx b)
  | .ternary a b c => .ternary (hExpr pfx a) (hExpr pfx b) (hExpr pfx c)
  | .concat xs => .concat (xs.map (hExpr pfx))
  | .resize w a => .resize w (hExpr pfx a)
  | .signedResize w a => .signedResize w (hExpr pfx a)
  | .squash2 w a => .squash2 w (hExpr pfx a)
  | .sysCall f a => .sysCall f (hExpr pfx a)
  | .typeBits n w => .typeBits n w
  | .reduce o a => .reduce o (hExpr pfx a)
  | .cast s a => .cast s (hExpr pfx a)
  | .repl n a => .repl (hExpr pfx n) (hExpr pfx a)
  | .functionCall n xs => .functionCall n (xs.map (hExpr pfx))
  | .aggregateMember n path =>
      .aggregateMember (pfx ++ n)
        (hExprPath pfx path)
  | e@(.paramRef ..) | e@(.genvarRef ..) | e@(.enumRef ..)
  | e@(.int ..) | e@(.fill ..) | e@(.lit ..) | e@(.unsupported ..) => e

private def hExprPath (pfx : String) : List (Option String × Option PExpr) →
    List (Option String × Option PExpr)
  | [] => []
  | (field, index) :: rest =>
      (field, hExprOpt pfx index) :: hExprPath pfx rest

private def hExprOpt (pfx : String) : Option PExpr → Option PExpr
  | none => none
  | some e => some (hExpr pfx e)
end

private def aggregateIndexRenameProbe : PExpr :=
  hExpr "u." (.aggregateMember "state"
    [(some "value", none), (none, some (.ident "sel_i"))])

#guard aggregateIndexRenameProbe ==
  .aggregateMember "u.state"
    [(some "value", none), (none, some (.ident "u.sel_i"))]

/-! A child is elaborated at its own parameter point before the hierarchy
merger hoists its source nodes into the parent's canonical memory design.
The merged design has only the parent's environment, so retain the parser's
nodes and replace the child's already-bound parameter/localparam references
with their concrete values (IEEE 1800-2023 §§6.20.2, 23.3.3). This is
elaboration substitution, not a semantic lowering: process and declaration
constructors remain the same nodes. -/

private def hParamExpr (vals : List (String × Int)) : PExpr → PExpr
  | .paramRef n none =>
      match vals.lookup n with
      | some v => .int v
      | none => .paramRef n none
  | .genvarRef n =>
      match vals.lookup n with
      | some v => .int v
      | none => .genvarRef n
  | .unary op a => .unary op (hParamExpr vals a)
  | .binary op a b => .binary op (hParamExpr vals a) (hParamExpr vals b)
  | .ternary c a b => .ternary (hParamExpr vals c) (hParamExpr vals a) (hParamExpr vals b)
  | .concat xs => .concat (xs.map (hParamExpr vals))
  | .resize w a => .resize w (hParamExpr vals a)
  | .signedResize w a => .signedResize w (hParamExpr vals a)
  | .squash2 w a => .squash2 w (hParamExpr vals a)
  | .sysCall f a => .sysCall f (hParamExpr vals a)
  | .bitSel a b => .bitSel (hParamExpr vals a) (hParamExpr vals b)
  | .partSel a b c => .partSel (hParamExpr vals a) (hParamExpr vals b) (hParamExpr vals c)
  | .repl a b => .repl (hParamExpr vals a) (hParamExpr vals b)
  | .reduce op a => .reduce op (hParamExpr vals a)
  | .cast s a => .cast s (hParamExpr vals a)
  | .arrayElem n xs => .arrayElem n (xs.map (hParamExpr vals))
  | .arrayPart n xs mode a b =>
      .arrayPart n (xs.map (hParamExpr vals)) mode (hParamExpr vals a) (hParamExpr vals b)
  | .functionCall n xs => .functionCall n (xs.map (hParamExpr vals))
  | .aggregateMember n path => .aggregateMember n path
  | e => e

private def hParamDim (vals : List (String × Int)) (d : PDim) : PDim :=
  { msb := hParamExpr vals d.msb, lsb := hParamExpr vals d.lsb }

private def hParamType (vals : List (String × Int)) : PType → PType
  | .packed dims resolved => .packed (dims.map (hParamDim vals)) resolved
  | ty => ty

private def hParamDecl (vals : List (String × Int)) (d : PDecl) : PDecl :=
  { d with type := hParamType vals d.type, unpackedDims := d.unpackedDims.map (hParamDim vals), init := d.init.map (hParamExpr vals) }

private def hParamLhs (vals : List (String × Int)) : PLhs → PLhs
  | .bitSel n i => .bitSel n (hParamExpr vals i)
  | .partSel n a b => .partSel n (hParamExpr vals a) (hParamExpr vals b)
  | .concat xs => .concat (xs.map (hParamLhs vals))
  | .arrayElem n xs => .arrayElem n (xs.map (hParamExpr vals))
  | .arrayPart n xs mode a b =>
      .arrayPart n (xs.map (hParamExpr vals)) mode (hParamExpr vals a) (hParamExpr vals b)
  | .aggregateMember n path =>
      .aggregateMember n (path.map fun (field, ix) => (field, ix.map (hParamExpr vals)))
  | l => l

private partial def hParamStmt (vals : List (String × Int)) : PStmt → PStmt
  | .blockingAssign n e => .blockingAssign n (hParamExpr vals e)
  | .nbaAssign n e => .nbaAssign n (hParamExpr vals e)
  | .ifStmt c a b => .ifStmt (hParamExpr vals c) (hParamStmt vals a) (b.map (hParamStmt vals))
  | .block xs => .block (xs.map (hParamStmt vals))
  | .forLoop i a c s b => .forLoop i (hParamExpr vals a) (hParamExpr vals c)
      (hParamExpr vals s) (hParamStmt vals b)
  | .blockingAssignL l e => .blockingAssignL (hParamLhs vals l) (hParamExpr vals e)
  | .nbaAssignL l e => .nbaAssignL (hParamLhs vals l) (hParamExpr vals e)
  | .caseStmt e xs d m c =>
      .caseStmt (hParamExpr vals e)
        (xs.map fun (ps, b) => (ps.map (hParamExpr vals), hParamStmt vals b))
        (d.map (hParamStmt vals)) m c
  | s@(.unsupported ..) => s

private def hParamProcess (vals : List (String × Int)) : PProcess → PProcess
  | .alwaysFF c b => .alwaysFF c (hParamStmt vals b)
  | .alwaysFFNegedge c b => .alwaysFFNegedge c (hParamStmt vals b)
  | .alwaysPlain c b => .alwaysPlain c (hParamStmt vals b)
  | .alwaysComb b => .alwaysComb (hParamStmt vals b)
  | .alwaysLatch b => .alwaysLatch (hParamStmt vals b)
  | .alwaysImplicit b => .alwaysImplicit (hParamStmt vals b)
  | .alwaysEvent events b => .alwaysEvent events (hParamStmt vals b)
  | .assign n e => .assign n (hParamExpr vals e)
  | .assignL l e => .assignL (hParamLhs vals l) (hParamExpr vals e)
  | .alwaysFFR c r b hi => .alwaysFFR c r (hParamStmt vals b) hi
  | .initial b => .initial (hParamStmt vals b)
  | p@(.unsupported ..) => p

private def hParamConn (vals : List (String × Int)) : PConn → PConn
  | .input p a net => .input p (a.map (hParamExpr vals)) net
  | .output p a => .output p (a.map (hParamLhs vals))
  | .inout p a => .inout p (a.map (hParamExpr vals))
  | c@(.unsupported ..) => c

private def hParamInst (vals : List (String × Int)) (i : PInst) : PInst :=
  { i with params := i.params.map (fun (n, e) => (n, hParamExpr vals e)), conns := i.conns.map (hParamConn vals) }

private partial def hParamGen (vals : List (String × Int)) : GenItem → GenItem
  | .process p => .process (hParamProcess vals p)
  | .decl d => .decl (hParamDecl vals d)
  | .localParam p => .localParam { p with expr := hParamExpr vals p.expr }
  | .genFor label g init bound step count body =>
      .genFor label g (hParamExpr vals init) (hParamExpr vals bound)
        (hParamExpr vals step) count (body.map (hParamGen vals))
  | .genIf cond yes no => .genIf (hParamExpr vals cond)
      (yes.map (hParamGen vals)) (no.map (hParamGen vals))
  | .unsupported k t => .unsupported k t
  | .inst i => .inst (hParamInst vals i)

private def hParamFunction (vals : List (String × Int)) (f : PFunction) : PFunction :=
  { f with formals := f.formals.map (hParamDecl vals), returnType := hParamType vals f.returnType, body := hParamExpr vals f.body }

private def hParamEnum (vals : List (String × Int)) (e : PEnumType) : PEnumType :=
  { e with base := hParamType vals e.base }

private def hParamDesign (vals : List (String × Int)) (d : PDesign) : PDesign :=
  { d with params := [], localParams := [], enums := d.enums.map (hParamEnum vals), decls := d.decls.map (hParamDecl vals), functions := d.functions.map (hParamFunction vals), processes := d.processes.map (hParamProcess vals), generates := d.generates.map (hParamGen vals) }

private def hParamVals (env : IEnv) : List (String × Int) :=
  env.vals ++ env.nvals.filterMap fun (n, (v, _, _)) =>
    if env.stale.contains n then none else some (n, v)

private def hLhs (pfx : String) : PLhs → PLhs
  | .ident n => .ident (pfx ++ n)
  | .bitSel n i => .bitSel (pfx ++ n) (hExpr pfx i)
  | .partSel n a b => .partSel (pfx ++ n) (hExpr pfx a) (hExpr pfx b)
  | .arrayElem n is => .arrayElem (pfx ++ n) (is.map (hExpr pfx))
  | .arrayPart n is m a b => .arrayPart (pfx ++ n) (is.map (hExpr pfx)) m (hExpr pfx a) (hExpr pfx b)
  | .aggregateMember n path =>
      .aggregateMember (pfx ++ n) (path.map fun (field, ix) => (field, ix.map (hExpr pfx)))
  | .concat xs => .concat (xs.map (hLhs pfx))

private partial def hStmt (pfx : String) : PStmt → PStmt
  | .blockingAssign n e => .blockingAssign (pfx ++ n) (hExpr pfx e)
  | .nbaAssign n e => .nbaAssign (pfx ++ n) (hExpr pfx e)
  | .blockingAssignL l e => .blockingAssignL (hLhs pfx l) (hExpr pfx e)
  | .nbaAssignL l e => .nbaAssignL (hLhs pfx l) (hExpr pfx e)
  | .ifStmt c a b => .ifStmt (hExpr pfx c) (hStmt pfx a) (b.map (hStmt pfx))
  | .block xs => .block (xs.map (hStmt pfx))
  | .forLoop i a c s b => .forLoop i (hExpr pfx a) (hExpr pfx c) (hExpr pfx s) (hStmt pfx b)
  | .caseStmt e xs d m c => .caseStmt (hExpr pfx e)
      (xs.map fun (ps, b) => (ps.map (hExpr pfx), hStmt pfx b))
      (d.map (hStmt pfx)) m c
  | e@(.unsupported ..) => e


private def hProcess (pfx : String) (clockMap : List (String × String)) : PProcess → PProcess
  | .alwaysFF c b => .alwaysFF (clockMap.lookup c |>.getD (pfx ++ c)) (hStmt pfx b)
  | .alwaysFFNegedge c b => .alwaysFFNegedge (clockMap.lookup c |>.getD (pfx ++ c)) (hStmt pfx b)
  | .alwaysPlain c b => .alwaysPlain (clockMap.lookup c |>.getD (pfx ++ c)) (hStmt pfx b)
  | .alwaysComb b => .alwaysComb (hStmt pfx b)
  | .alwaysLatch b => .alwaysLatch (hStmt pfx b)
  | .alwaysImplicit b => .alwaysImplicit (hStmt pfx b)
  | .alwaysEvent events b => .alwaysEvent (events.map fun e => { e with signal := pfx ++ e.signal }) (hStmt pfx b)
  | .alwaysFFR c r b hi => .alwaysFFR (clockMap.lookup c |>.getD (pfx ++ c))
      (clockMap.lookup r |>.getD (pfx ++ r)) (hStmt pfx b) hi
  | .assign n e => .assign (pfx ++ n) (hExpr pfx e)
  | .assignL l e => .assignL (hLhs pfx l) (hExpr pfx e)
  | .initial b => .initial (hStmt pfx b)
  | e@(.unsupported ..) => e

private def hItems : List GenItem → Option PInst
  | [] => none
  | .inst i :: _ => some i
  | .process _ :: rest | .decl _ :: rest | .localParam _ :: rest
  | .unsupported .. :: rest => hItems rest
  | _ :: rest => hItems rest
termination_by structural xs => xs

private def childDesign (top : PDesign) (lib : List PDesign) (args : List Int) :
    Except String (PDesign × PInst × String) := do
  let env ← match top.paramEnvH { int32 := true } args with
    | .ok e => pure e
    | .timeout => throw "parameter elaboration timed out"
    | .unsupported e => throw e
  let some inst := hItems top.generates
    | throw "no child instance in source-shaped hierarchy"
  let some child := lib.find? (·.name == inst.module)
    | throw s!"module '{inst.module}' is not in the envelope library"
  let given ← inst.given env child
  let (child', _) ← child.atPoint given
  let pfx ← inst.prefix env
  pure (child', inst, pfx)

private partial def generatedInstances (env : IEnv) (fuel : Nat) :
    List GenItem → Res (List (PInst × IEnv))
  | [] => .ok []
  | .inst i :: rest => do
      let tail ← generatedInstances env fuel rest
      .ok ((hParamInst (hParamVals env) i, env) :: tail)
  | .process _ :: rest | .decl _ :: rest | .localParam _ :: rest =>
      generatedInstances env fuel rest
  | .unsupported k t :: _ => .unsupported s!"{k}: {t}"
  | .genIf cond yes no :: rest => do
      let chosen := if (evalInt env cond).toOption.getD 0 != 0 then yes else no
      let here ← generatedInstances env fuel chosen
      let tail ← generatedInstances env fuel rest
      .ok (here ++ tail)

  | .genFor _ g init bound step _ body :: rest => do
      let i ← match evalInt env init with | .ok x => .ok x | .error e => .unsupported e
      let delta ← match stepDelta g step with | .ok x => .ok x | .error e => .unsupported e
      let values ← genvarSeq env g bound delta fuel i
      let here ← values.foldlM (init := []) fun acc v => do
        let xs ← generatedInstances (env.bindVal g v) fuel body
        .ok (acc ++ xs)
      let tail ← generatedInstances env fuel rest
      .ok (here ++ tail)

/-! The hierarchy adapter has two source-shaped walks over the active generate
tree. `generatedInstances` above finds child module instances; this companion
walk retains the other active nodes for the parent design.  A generate-local
declaration is collected by `coreMemGeneratedDeclsList`, while this walk keeps
the source process nodes.  Instance nodes are consumed by the hierarchy merge
and therefore do not become a spurious `Instance` process in the merged E
design (IEEE 1800-2023 §§23.3.3, 27). -/
mutual
private def generatedParentItem (env : IEnv) (fuel : Nat) (vals : List (String × Int)) :
    GenItem → Res (List PProcess)
  | .process p => .ok [coreMemSubstProcess { genvars := vals } p]
  | .decl _ | .localParam _ | .inst _ => .ok []
  | .unsupported k t => .ok [.unsupported k t]
  | .genIf cond thenB elseB =>
      match evalGenGuard (coreMemBindVals env { genvars := vals }) cond with
      | .error e => .unsupported s!"generate if: {e}"
      | .ok v => if v != 0 then generatedParentList env fuel vals thenB
                 else generatedParentList env fuel vals elseB
  | .genFor _label g initE bound step _rc body =>
      let env' := coreMemBindVals env { genvars := vals }
      match evalInt env' initE, stepDelta g step with
      | .ok i0, .ok δ => do
          let vs ← genvarSeq env' g bound δ fuel i0
          generatedParentIters env fuel vals g vs body
      | .error e, _ => .unsupported s!"generate for: {e}"
      | _, .error e => .unsupported s!"generate for: {e}"
  termination_by it => (sizeOf it, 0)
  decreasing_by all_goals (simp_wf; omega)

private def generatedParentList (env : IEnv) (fuel : Nat) (vals : List (String × Int)) :
    List GenItem → Res (List PProcess)
  | [] => .ok []
  | it :: rest => do
      let ps ← generatedParentItem env fuel vals it
      let qs ← generatedParentList env fuel vals rest
      .ok (ps ++ qs)
  termination_by xs => (sizeOf xs, 0)
  decreasing_by all_goals (simp_wf; omega)

private def generatedParentIters (env : IEnv) (fuel : Nat) (vals : List (String × Int))
    (g : String) : List Int → List GenItem → Res (List PProcess)
  | [], _ => .ok []
  | v :: vs, body => do
      let ps ← generatedParentList env fuel ((g, v) :: vals) body
      let qs ← generatedParentIters env fuel vals g vs body
      .ok (ps ++ qs)
  termination_by vs body => (sizeOf body, vs.length + 1)
  decreasing_by all_goals (simp_wf; omega)
end

private structure HChild where
  child : PDesign
  args : List Int
  inst : PInst
  pfx : String
  parentPfx : String
  generated : List PProcess

private def childFor (env : IEnv) (lib : List PDesign) (i : PInst) (parentPfx : String := "") :
    Res HChild :=
  match lib.find? (·.name == i.module) with
  | none => .unsupported s!"module '{i.module}' is not in the envelope library"
  | some child =>
      match i.given env child, i.prefix env with
      | .error e, _ => .unsupported e
      | _, .error e => .unsupported e
      | .ok given, .ok pfx =>
          match child.atPoint given with
          | .ok (child', cargs) => do
              -- A child generate is source-shaped until its own parameter
              -- point is known.  Expand that retained node at the child's
              -- point before hoisting the process into the parent; dropping
              -- it here turns a driven output into an initial x (IEEE
              -- 1800-2023 §§27.4, 23.3.3).
              let cenv ← child'.paramEnvH { int32 := true, functions := child'.functions } cargs
              let child'' := hParamDesign (hParamVals cenv) child'
              let generated ← generatedParentList cenv
                (PDesign.surfaceFuel cargs) [] child''.generates
              -- A child declaration or port boundary is discovered before
              -- its processes are hoisted into the parent.  Letting an
              -- unsupported aggregate node reach the process compiler loses
              -- the parser-native wall (and previously hit an incomplete
              -- constructor match on the child path).  Preserve the exact
              -- child member refusal under IEEE 1800-2023 §23.3.3 instead
              -- of flattening or re-parsing the aggregate.
              match coreMemFirstUnsupportedOther child'' generated child''.others with
              | some (kind, text) =>
                  .unsupported s!"E memory route does not yet admit module member '{kind}' ({text})"
              | none =>
                  .ok { child := child'', args := cargs, inst := i,
                        pfx := parentPfx ++ pfx, parentPfx, generated }
          | .error e => .unsupported e

/-- Build a one-child source-shaped memory design. The child may contain the
parameter-sized unpacked storage; parent and child parameter names remain
source-shaped, so `PDesign.instantiateCoreMem` binds dimensions at the top point. -/
def CoreMemDesign.ofHierarchy (top : PDesign) (lib : List PDesign) (args : List Int) :
    Res CoreMemDesign :=
  do
  let env ← match top.paramEnvH { int32 := true, functions := top.functions } args with
    | .ok e => .ok e
    | .timeout => .timeout
    | .unsupported e => .unsupported e
  let (generatedDecls, _) ← coreMemGeneratedDeclsList env
    (PDesign.surfaceFuel args) {} top.generates
  let generatedPs ← generatedParentList env
    (PDesign.surfaceFuel args) [] top.generates
  let insts ← generatedInstances env (PDesign.surfaceFuel args) top.generates
  let direct ← insts.mapM fun (i, ie) => childFor ie lib i
  let rec nested (fuel : Nat) (parent : HChild) : Res (List HChild) := do
    match fuel with
    | 0 => .unsupported "23.3: hierarchy expansion fuel exhausted"
    | fuel + 1 =>
    let cenv ← match parent.child.paramEnvH { int32 := true, functions := parent.child.functions } parent.args with
      | .ok e => .ok e
      | .timeout => .timeout
      | .unsupported e => .unsupported e
    let insts ← generatedInstances cenv (PDesign.surfaceFuel parent.args) parent.child.generates
    let here ← insts.mapM fun (i, ie) => childFor ie lib i parent.pfx
    let tails ← here.mapM (nested fuel)
    .ok (here ++ tails.flatten)
  let tails ← direct.mapM (nested (PDesign.surfaceFuel args))
  let children := direct ++ tails.flatten
  let childDecls := children.flatMap fun c => c.child.decls.map fun pd => { pd with
      name := c.pfx ++ pd.name
      isInput := false
      isOutput := false }
  let childPs := children.flatMap fun c =>
    let clockMap := c.inst.conns.filterMap fun conn =>
      match conn with
      | .input port (some (.ident actual)) _ => some (port, c.parentPfx ++ actual)
      | _ => none
    (c.child.processes ++ c.generated).map (hProcess c.pfx clockMap)
  let inputPs := children.flatMap fun c => c.inst.conns.filterMap fun conn =>
      match conn with
      | .input port (some actual) _ =>
          match actual with
          | .arrayElem _ [] => some (.assignL (.arrayElem (c.pfx ++ port) []) (hExpr c.parentPfx actual))
          | _ => some (.assign (c.pfx ++ port) (hExpr c.parentPfx actual))
      | _ => none
  let outputPs := children.flatMap fun c => c.inst.conns.filterMap fun conn =>
      match conn with
      | .output port (some target) => some (.assignL (hLhs c.parentPfx target) (.ident (c.pfx ++ port)))
      | _ => none
  let merged := { top with
      decls := top.decls ++ generatedDecls ++ childDecls
      -- Port connections are continuous drivers.  Place child processes
      -- before generated output drivers, and parent processes after those
      -- drivers, so the canonical one-pass settle sees both combinational
      -- child outputs and edge-child updates before parent assignments
      -- (IEEE 1800-2023 §§4.5, 23.2.2).  This is an elaboration-order
      -- choice, not a source rewrite.
      processes := inputPs ++ childPs ++ outputPs ++ top.processes ++ generatedPs
      generates := []
      others := top.others ++ children.flatMap fun c => c.child.others
      -- A child function remains a source-shaped declaration after the
      -- §23.3.3 port-connection merge.  Carry it into the merged constant
      -- scope so a child localparam such as `vbits(N)` is evaluated by the
      -- same canonical constant-function tier as the top declaration.
      functions := top.functions ++ children.flatMap fun c => c.child.functions }
  match PDesign.instantiateCoreMem merged args with
  | .ok d => .ok d
  | .timeout => .timeout
  | .unsupported e => .unsupported e

/-! Ordinary hierarchy entry: the same canonical memory representation is
used after parser-native child elaboration and port connection merging. -/
def PDesign.instantiateE2H (d : PDesign) (lib : List PDesign) (args : List Int) :
    Res CoreMemDesign :=
  CoreMemDesign.ofHierarchy d lib args
  /- The old one-child path is retained in the source below as a reference for
     the port-connection shape; generated instances use the same hProcess rule. -/
  /-
  match childDesign top lib args with
  | .error e => .unsupported s!"Instance:memory: {e}"
  | .ok (child, inst, pfx) =>
    let childDecls := child.decls.map fun pd => { pd with
      name := pfx ++ pd.name
      isInput := false
      isOutput := false }
    let clockMap := inst.conns.filterMap fun c =>
      match c with | .input port (some (.ident actual)) _ => some (port, actual) | _ => none
    let childPs := child.processes.map (hProcess pfx clockMap)
    let inputPs := inst.conns.filterMap fun c =>
      match c with
      | .input port (some actual) _ => some (.assign (pfx ++ port) actual)
      | _ => none
    let outputPs := inst.conns.filterMap fun c =>
      match c with
      | .output port (some (.ident target)) => some (.assign target (.ident (pfx ++ port)))
      | _ => none
    let merged := { top with
      decls := top.decls ++ childDecls
      processes := top.processes ++ inputPs ++ childPs ++ outputPs
      generates := []
      others := top.others ++ child.others }
    match PDesign.instantiateCoreMem merged args with
    | .ok d => .ok d
    | .timeout => .timeout
    | .unsupported e => .unsupported e -/


end LeanModels.Sv.Kernel
