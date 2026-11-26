import LeanModels.Sv.Kernel.CoreMemResume
import LeanModels.Sv.Kernel.XResolve
import LeanModels.Sv.Kernel.Core1Edge
import LeanModels.Sv.Obs

/-! # A choice-explicit step for the clocked Active and NBA regions

**Status: T1 implementation seam.** The relation is normative only for the
admitted fragment below. The executor remains an implementation instrument.

The meaning given here is the closure of ONE total step function
`ndStep E choice s`.  It has no fuel argument and no bound on the number of
steps.  Its two choice points are explicit:

* **Scheduling** (IEEE 1800-2023 §4.7): `choice : Nat` is an index into the
  list of runnable cursors.  The chosen cursor executes exactly one parser
  node (`EdgeWork`, the cursor of `CoreMemResume`) and returns to the list.
  Nothing here says whether a process may be preempted between two of its own
  nodes: the relation offers every index at every step, and a coarser
  (process-atomic) meaning is the restriction of the same relation to runs
  that keep choosing the same cursor until it is empty. Granularity remains an
  owner question.
* **Unknown reads** (the x rule, `docs/sv-x-interface.md`): the state carries
  an `Oracle`, an unbounded supply of answers.  A decision that consults a
  value with unknown bits takes one answer per unknown bit and the supply is
  advanced (`Oracle.read`).  The same site in a later step or a later cycle
  therefore asks a fresh question.  There is no enumeration of values and no
  fixed function that is asked again.  `Oracle.read_xread` and
  `Oracle.read_complete` say that the answers are exactly the per-read
  relation `XRead`.

`Nd.Step E s t` holds when some choice produces `t`; `Run` is its
reflexive-transitive closure; `NdState.settled` marks the terminal states;
`Nd.EventSettles` is the derived relation from one input event to a settled
state.

## What is covered, and what is refused loudly

Covered: `always_ff`/`always @(edge ...)` processes (`CoreMemProc.edge`,
`CoreMemProc.event`) whose bodies are built from blocks, `if`, counted `for`,
blocking and nonblocking assignments and declarations; the NBA region commit;
events caused by that commit (a further round in the same time slot, with no
bound on the number of rounds).

Refused by name (`NdOutcome.refused`), never approximated:
* a design with a continuous assignment, a primitive, `always_comb`,
  `always_latch`, `always @*`, a resolved net or an unsupported process
  (`CoreMemDesign.ndAdmitted`): the continuous and combinational regions are
  not in this relation yet;
* a `case` statement: which reads of the selector and of the items resolve is
  not settled between the two x documents;
* case equality/inequality, wildcard equality, `casex` and `casez`, and an
  unknown write index, because their per-read x behavior is not opened here;
* x/z on a clock or event expression;
* a blocking write that changes an event-source signal. The NBA may then
  produce a second edge from an intermediate value while the old wake base is
  retained.
* time-zero `initial` processes, declaration initializers, and `$readmemh`
  metadata. Their ordering and execution belong to a separate time-zero
  relation and are rejected at admission until that relation is present.

What had to be reimplemented because the existing one-step function
(`EdgeWork.openNode`) has its choices built in: the `if` arm (it called
`condTrue` on the four-state value, which takes the else branch on an
unknown) and the `case` arm (it ran the whole statement through
`execStmtFuel ... 4096`).  Every other arm is the existing function.  Leaf
statements call the existing executor on that one statement; the fuel literal
`1` there is not a bound, `execStmtFuel` does not recurse on a leaf.

The reused leaf evaluator retains implementation budgets of 4096 in
`resolveLhs2` and `resolveConcatLhs2`. Expression values use the existing
`Expr2` lowering and its four-state ternary and memory-read-index merge,
which is a deliberate superset until the owner decides whether those reads
also become oracle sites. Elaboration's `iterFuel = 4096` is outside this
relation.

Open owner questions are scheduling granularity, x on clocks and event
controls, inputs-first ordering within a row, atomicity of NBA commit, the
ternary and memory-index x rule, and the elaboration budget boundary.

A consequence of refusing x/z on a control value: `NdState.begin` refuses
from a power-on store whose clocks are x, so the relation has no run from
`E.initial` for a clocked design.  Until the owner decides how the first
known clock value is modelled, every statement over this relation is about a
start store whose control signals are known; the theorems name that
hypothesis (`CoreMemDesign.ControlsKnown`, `NdSound.lean`).
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

set_option autoImplicit false

/-! ## The oracle for unknown reads -/

/-- An unbounded supply of answers for unknown bits.  It is consumed: a read
of `k` unknown bits takes the first `k` answers and leaves `Oracle.drop k`. -/
abbrev Oracle := Nat → Bool

/-- The supply after `k` answers have been taken. -/
def Oracle.drop (o : Oracle) (k : Nat) : Oracle := fun n => o (n + k)

/-- The supply that answers `b` first and then continues as `o`. -/
def Oracle.cons (b : Bool) (o : Oracle) : Oracle
  | 0 => b
  | n + 1 => o n

/-- The supply that always answers 0.  The existing executor's choice at an
unknown decision (`condTrue` is false when no bit is a known 1) is this
supply; see `Oracle.zero_read_condTrue`. -/
def Oracle.zero : Oracle := fun _ => false

@[simp] theorem Oracle.drop_cons (b : Bool) (o : Oracle) : (Oracle.cons b o).drop 1 = o := rfl

@[simp] theorem Oracle.cons_zero (b : Bool) (o : Oracle) : (Oracle.cons b o) 0 = b := rfl

@[simp] theorem Oracle.zero_drop (k : Nat) : Oracle.zero.drop k = Oracle.zero := rfl

/-- Resolve a bit list: a known bit is kept, an unknown bit takes the next
answer.  Returns the 0/1 list and the remaining supply. -/
def Oracle.bits (o : Oracle) : List Logic → List Logic × Oracle
  | [] => ([], o)
  | b :: bs =>
      if b.isKnown then
        ((b :: (Oracle.bits o bs).1), (Oracle.bits o bs).2)
      else
        ((if o 0 then Logic.l1 else Logic.l0) :: (Oracle.bits (o.drop 1) bs).1,
          (Oracle.bits (o.drop 1) bs).2)

/-- One read of a four-state value at a resolution site. -/
def Oracle.read (o : Oracle) (v : LVec) : LVec × Oracle :=
  (⟨(o.bits v.bits.toList).1.toArray⟩, (o.bits v.bits.toList).2)

theorem Oracle.bits_mem (o : Oracle) (bs : List Logic) :
    (o.bits bs).1 ∈ resolveBits bs := by
  induction bs generalizing o with
  | nil => simp [Oracle.bits, resolveBits]
  | cons b bs ih =>
      cases b
      · simp [Oracle.bits, resolveBits, Logic.resolutions, Logic.isKnown, ih]
      · simp [Oracle.bits, resolveBits, Logic.resolutions, Logic.isKnown, ih]
      · by_cases h : o 0 <;>
          simp [Oracle.bits, resolveBits, Logic.resolutions, Logic.isKnown, ih, h]
      · by_cases h : o 0 <;>
          simp [Oracle.bits, resolveBits, Logic.resolutions, Logic.isKnown, ih, h]

/-- Every answer of the oracle is a per-read resolution (`XRead`) of the
value that was read. -/
theorem Oracle.read_xread (o : Oracle) (v : LVec) : XRead v (o.read v).1 := by
  unfold XRead LVec.concretizations Oracle.read
  exact List.mem_map.mpr ⟨_, Oracle.bits_mem o _, rfl⟩

theorem Oracle.bits_complete (bs cs : List Logic) (h : cs ∈ resolveBits bs) (o' : Oracle) :
    ∃ o : Oracle, o.bits bs = (cs, o') := by
  induction bs generalizing cs with
  | nil =>
      have : cs = [] := by simpa [resolveBits] using h
      subst this
      exact ⟨o', rfl⟩
  | cons b bs ih =>
      rw [resolveBits, List.mem_flatMap] at h
      obtain ⟨c, hc, hcs⟩ := h
      rw [List.mem_map] at hcs
      obtain ⟨rest, hrest, rfl⟩ := hcs
      obtain ⟨o1, ho1⟩ := ih rest hrest
      cases b
      · have : c = Logic.l0 := by simpa [Logic.resolutions] using hc
        subst this
        exact ⟨o1, by simp [Oracle.bits, Logic.isKnown, ho1]⟩
      · have : c = Logic.l1 := by simpa [Logic.resolutions] using hc
        subst this
        exact ⟨o1, by simp [Oracle.bits, Logic.isKnown, ho1]⟩
      · have : c = Logic.l0 ∨ c = Logic.l1 := by simpa [Logic.resolutions] using hc
        rcases this with rfl | rfl
        · exact ⟨Oracle.cons false o1, by simp [Oracle.bits, Logic.isKnown, ho1]⟩
        · exact ⟨Oracle.cons true o1, by simp [Oracle.bits, Logic.isKnown, ho1]⟩
      · have : c = Logic.l0 ∨ c = Logic.l1 := by simpa [Logic.resolutions] using hc
        rcases this with rfl | rfl
        · exact ⟨Oracle.cons false o1, by simp [Oracle.bits, Logic.isKnown, ho1]⟩
        · exact ⟨Oracle.cons true o1, by simp [Oracle.bits, Logic.isKnown, ho1]⟩

/-- Every per-read resolution is the answer of some oracle, and the supply
that remains afterwards can be any supply.  So a statement proved for every
oracle is a statement for every sequence of independent resolutions. -/
theorem Oracle.read_complete {v c : LVec} (h : XRead v c) (o' : Oracle) :
    ∃ o : Oracle, o.read v = (c, o') := by
  unfold XRead LVec.concretizations at h
  obtain ⟨cs, hcs, rfl⟩ := List.mem_map.mp h
  obtain ⟨o, ho⟩ := Oracle.bits_complete _ _ hcs o'
  exact ⟨o, by simp [Oracle.read, ho]⟩

theorem Oracle.bits_known (o : Oracle) (bs : List Logic)
    (h : bs.all Logic.isKnown = true) : o.bits bs = (bs, o) := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      simp only [List.all_cons, Bool.and_eq_true] at h
      simp [Oracle.bits, h.1, ih h.2]

/-- A read of a value with no unknown bit returns that value and takes no
answer. -/
theorem Oracle.read_known (o : Oracle) (v : LVec)
    (h : v.bits.toList.all Logic.isKnown = true) : o.read v = (v, o) := by
  simp [Oracle.read, Oracle.bits_known o _ h]

theorem Oracle.zero_bits (bs : List Logic) :
    (Oracle.zero.bits bs).2 = Oracle.zero ∧
      (Oracle.zero.bits bs).1.any (· == Logic.l1) = bs.any (· == Logic.l1) := by
  induction bs with
  | nil => exact ⟨rfl, rfl⟩
  | cons b bs ih =>
      cases b <;> simp [Oracle.bits, Logic.isKnown, ih.1, ih.2, Oracle.zero] <;> rfl

/-- The always-0 supply stays the always-0 supply. -/
theorem Oracle.zero_read_snd (v : LVec) : (Oracle.zero.read v).2 = Oracle.zero :=
  (Oracle.zero_bits _).1

/-- Under the always-0 supply a decision is the existing executor's
`condTrue` of the four-state value: an unknown that is not accompanied by a
known 1 selects the else branch. -/
theorem Oracle.zero_read_condTrue (v : LVec) :
    (Oracle.zero.read v).1.condTrue = v.condTrue := by
  have h := (Oracle.zero_bits v.bits.toList).2
  simp only [Oracle.read, LVec.condTrue]
  rw [List.any_toArray, h, Array.any_toList]

/-! ## States and outcomes -/

/-- A state of the clocked Active/NBA machine. -/
structure NdState where
  /-- The shared store: scalars, memories, aggregates. -/
  store : CoreMemState
  /-- The runnable cursors.  A cursor holds the parser nodes one activation
      still has to execute, and its automatic locals. -/
  active : List EdgeCursor
  /-- Scalar nonblocking updates issued so far in this round, in issue order. -/
  scalarQ : NbaQueue2
  /-- Memory nonblocking updates issued so far in this round. -/
  memoryQ : MemNbaQueue
  /-- The scalar view at the last point where waiting processes were woken.
      The NBA commit compares its result with this view (§9.4.2). -/
  base : SvState
  /-- The remaining supply of answers for unknown reads. -/
  oracle : Oracle
  /-- The time slot has no further event. -/
  settled : Bool

/-- The result of asking the step function for one move. -/
inductive NdOutcome where
  /-- The move exists and leads to this state. -/
  | next (s : NdState)
  /-- The construct met by this move is outside the relation.  This is a
      named refusal, never a value. -/
  | refused (why : String)
  /-- The choice does not name a move in this state. -/
  | disabled

/-- Split a list at an index. -/
def pickAt {α : Type} : Nat → List α → Option (List α × α × List α)
  | _, [] => none
  | 0, c :: rest => some ([], c, rest)
  | i + 1, c :: rest =>
      match pickAt i rest with
      | some (before, x, after) => some (c :: before, x, after)
      | none => none

theorem pickAt_append {α : Type} (before : List α) (c : α) (after : List α) :
    pickAt before.length (before ++ c :: after) = some (before, c, after) := by
  induction before with
  | nil => rfl
  | cons b bs ih => simp [pickAt, ih]

theorem pickAt_eq {α : Type} : ∀ {i : Nat} {l before : List α} {c : α} {after : List α},
    pickAt i l = some (before, c, after) → l = before ++ c :: after
  | _, [], _, _, _, h => by simp [pickAt] at h
  | 0, x :: rest, _, _, _, h => by
      simp only [pickAt, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      rfl
  | i + 1, x :: rest, before, c, after, h => by
      simp only [pickAt] at h
      cases hp : pickAt i rest with
      | none => simp [hp] at h
      | some r =>
          obtain ⟨b', x', a'⟩ := r
          simp only [hp, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          simp [pickAt_eq hp]

/-- A cursor stays in the runnable list while it has work. -/
def EdgeCursor.keep (c : EdgeCursor) : List EdgeCursor :=
  if c.work.isEmpty then [] else [c]

/-- The result of a node that changes nothing. -/
def CoreMemExecResult.idle (st : CoreMemState) (locals : SvState) : CoreMemExecResult :=
  { state := st, scalarQ := [], memoryQ := [], locals }

/-! ## One parser node, with the unknown read opened -/

/-- Execute one leaf statement with the existing executor.  `execStmtFuel`
does not recurse on these statements, so the fuel literal `1` is not a bound.
That is proved for the two whole-signal nonblocking leaves
(`execStmtFuel_nbaAssign_fuel`, `execStmtFuel_nbaAssignIdent_fuel` in
`NdSound.lean`); for the blocking and declaration leaves it holds by reading
`execStmtFuel` and is not yet a lemma. -/
def ndLeaf (E : CoreMemDesign) (st : CoreMemState) (locals : SvState) (o : Oracle)
    (env : IEnv) (stmt : PStmt) : Res (CoreMemExecResult × List EdgeWork × Oracle) :=
  match E.execStmtFuel env E.elems st locals 1 stmt with
  | .ok r => .ok (r, [], o)
  | .timeout => .timeout
  | .unsupported msg => .unsupported msg

/-! The choice-explicit relation does not yet open case-equality and wildcard
observers as independent x-read choices.  Refuse those parser nodes before the
four-state leaf evaluator can collapse them to one answer. -/
mutual
def ndXObserver? : PExpr → Option String
  | .binary op left right =>
      match op with
      | .ceq => some "12.4: case equality '===' is outside per-read x semantics"
      | .cne => some "12.4: case inequality '!==' is outside per-read x semantics"
      | .m0 .caseEq => some "12.4: case equality '===' is outside per-read x semantics"
      | .m0 .caseNe => some "12.4: case inequality '!==' is outside per-read x semantics"
      | .m0 .wildEq => some "12.5.4: wildcard equality '==?' is outside per-read x semantics"
      | .m0 .wildNe => some "12.5.4: wildcard inequality '!=?' is outside per-read x semantics"
      | .m0 .casez => some "12.5.4: casez is outside per-read x semantics"
      | .m0 .casex => some "12.5.4: casex is outside per-read x semantics"
      | _ => (ndXObserver? left).or (ndXObserver? right)
  | .unary _ arg | .resize _ arg | .signedResize _ arg | .squash2 _ arg
  | .sysCall _ arg | .reduce _ arg | .cast _ arg => ndXObserver? arg
  | .ternary cond yes no => (ndXObserver? cond).or ((ndXObserver? yes).or (ndXObserver? no))
  | .concat parts => ndXObserverList? parts
  | .bitSel base index | .repl base index => (ndXObserver? base).or (ndXObserver? index)
  | .partSel base msb lsb => (ndXObserver? base).or ((ndXObserver? msb).or (ndXObserver? lsb))
  | .arrayElem _ indices => ndXObserverList? indices
  | .arrayPart _ indices _ a b =>
      (ndXObserverList? indices).or ((ndXObserver? a).or (ndXObserver? b))
  | .aggregateMember _ _ => none
  | .packageAggElem _ _ index => ndXObserver? index
  | .functionCall _ args => ndXObserverList? args
  | .lit _ | .ident _ | .paramRef _ _ | .genvarRef _ | .enumRef _ _ _
  | .int _ | .fill _ | .typeBits _ _ | .unsupported _ _ => none
termination_by structural e => e

def ndXObserverList? : List PExpr → Option String
  | [] => none
  | e :: es => (ndXObserver? e).or (ndXObserverList? es)
termination_by structural es => es
end

def ndIndexExprs : PLhs → List PExpr
  | .ident _ => []
  | .bitSel _ index => [index]
  | .partSel _ msb lsb => [msb, lsb]
  | .concat parts => parts.flatMap ndIndexExprs
  | .arrayElem _ indices => indices
  | .arrayBitSel _ indices bit => indices ++ [bit]
  | .arrayPart _ indices _ a b => indices ++ [a, b]
  | .aggregateMember _ path => path.filterMap (fun (_, index) => index)

def CoreMemDesign.ndCheckExpr (E : CoreMemDesign) (expr : PExpr) : Res Unit :=
  match ndXObserver? expr with
  | none => .ok ()
  | some msg => .unsupported msg

def CoreMemDesign.ndCheckIndexExprs (E : CoreMemDesign) (env : IEnv)
    (st : CoreMemState) (locals : SvState) : List PExpr → Res Unit
  | [] => .ok ()
  | index :: rest =>
      match E.ndCheckExpr index with
      | .timeout => .timeout
      | .unsupported msg => .unsupported msg
      | .ok () =>
          match E.evalIndexLocals env E.elems st locals index with
          | .timeout => .timeout
          | .unsupported msg => .unsupported msg
          | .ok value =>
              if value.bits.toList.all Logic.isKnown then
                E.ndCheckIndexExprs env st locals rest
              else
                .unsupported "11.5.1: unknown write index is outside per-read x semantics"

def CoreMemDesign.ndCheckTarget (E : CoreMemDesign) (env : IEnv)
    (st : CoreMemState) (locals : SvState) (target : PLhs) : Res Unit :=
  E.ndCheckIndexExprs env st locals (ndIndexExprs target)

def CoreMemDesign.ndCheckOptionalExpr (E : CoreMemDesign) : Option PExpr → Res Unit
  | none => .ok ()
  | some expr => E.ndCheckExpr expr

/-- Inspect one statement node. -/
def ndOpenStmt (E : CoreMemDesign) (st : CoreMemState) (locals : SvState) (o : Oracle)
    (env : IEnv) : PStmt → Res (CoreMemExecResult × List EdgeWork × Oracle)
  | .block body => .ok (.idle st locals, [.edgeBlock env body], o)
  | .ifStmt cond yes no =>
      match E.ndCheckExpr cond with
      | .unsupported msg => .unsupported msg
      | .timeout => .timeout
      | .ok () =>
      -- §12.4: the condition is a resolution site.  The four-state value is
      -- read once through the oracle; the branch is decided on the 0/1 result.
          match E.evalExprLocals env E.elems st (some 1) locals cond with
          | .ok cv =>
              .ok (.idle st locals,
                (if (o.read cv).1.condTrue then some yes else no).toList.map (EdgeWork.edgeStmt env),
                (o.read cv).2)
          | .timeout => .timeout
          | .unsupported msg => .unsupported msg
  | .forLoop name init cond step body =>
      match forValues2 env name init cond step with
      | .ok values => .ok (.idle st locals, [.edgeLoop env name body values], o)
      | .unsupported msg => .unsupported s!"ForLoopStatement: {msg}"
      | .timeout => .timeout
  | .caseStmt _ _ _ mode _ =>
      match mode with
      | .casex => .unsupported "12.5.4: casex is outside per-read x semantics"
      | .casez => .unsupported "12.5.4: casez is outside per-read x semantics"
      | _ => .unsupported "12.5: case statement is not opened in the choice-explicit step (selector and item reads)"
  | .blockingAssign target value =>
      match E.ndCheckExpr value with
      | .ok () => ndLeaf E st locals o env (.blockingAssign target value)
      | .timeout => .timeout
      | .unsupported msg => .unsupported msg
  | .blockingAssignL target value =>
      match E.ndCheckExpr value, E.ndCheckTarget env st locals target with
      | .ok (), .ok () => ndLeaf E st locals o env (.blockingAssignL target value)
      | .timeout, _ | _, .timeout => .timeout
      | .unsupported msg, _ | _, .unsupported msg => .unsupported msg
  | .nbaAssign target value =>
      match E.ndCheckExpr value with
      | .ok () => ndLeaf E st locals o env (.nbaAssign target value)
      | .timeout => .timeout
      | .unsupported msg => .unsupported msg
  | .nbaAssignL target value =>
      match E.ndCheckExpr value, E.ndCheckTarget env st locals target with
      | .ok (), .ok () => ndLeaf E st locals o env (.nbaAssignL target value)
      | .timeout, _ | _, .timeout => .timeout
      | .unsupported msg, _ | _, .unsupported msg => .unsupported msg
  | .localDecl name width init =>
      match E.ndCheckOptionalExpr init with
      | .ok () => ndLeaf E st locals o env (.localDecl name width init)
      | .timeout => .timeout
      | .unsupported msg => .unsupported msg
  | .automaticDecl name width init =>
      match E.ndCheckOptionalExpr init with
      | .ok () => ndLeaf E st locals o env (.automaticDecl name width init)
      | .timeout => .timeout
      | .unsupported msg => .unsupported msg
  | .unsupported kind text => .unsupported s!"{kind}: {text}"

/-- Inspect one pending node of a cursor.  Returns the node's effect, the
nodes it exposes, and the remaining oracle. -/
def EdgeWork.ndOpen (E : CoreMemDesign) (st : CoreMemState) (locals : SvState) (o : Oracle) :
    EdgeWork → Res (CoreMemExecResult × List EdgeWork × Oracle)
  | .edgeBlock _ [] => .ok (.idle st locals, [], o)
  | .edgeBlock env (stmt :: rest) =>
      .ok (.idle st locals, [.edgeStmt env stmt, .edgeBlock env rest], o)
  | .edgeLoop _ _ _ [] => .ok (.idle st locals, [], o)
  | .edgeLoop env name body (value :: rest) =>
      .ok (.idle st locals,
        [.edgeStmt (env.bindVal name value) body, .edgeLoop env name body rest], o)
  | .edgeStmt env stmt => ndOpenStmt E st locals o env stmt

/-! ## The step function -/

/-- The processes whose event occurs between two scalar views, as fresh
cursors in source order (§9.4.2). -/
def CoreMemProc.ndWake (E : CoreMemDesign) (before after : SvState) :
    CoreMemProc → Option EdgeCursor
  | .edge p => if p.fires before after then some (EdgeCursor.start E.env p.body) else none
  | .event events body =>
      if coreMemEventsFire before after events then some (EdgeCursor.start E.env body) else none
  | _ => none

def CoreMemDesign.ndWakeList (E : CoreMemDesign) (before after : SvState)
    (procs : List CoreMemProc) : List EdgeCursor :=
  procs.filterMap (CoreMemProc.ndWake E before after)

def CoreMemDesign.ndWake (E : CoreMemDesign) (before after : SvState) : List EdgeCursor :=
  E.ndWakeList before after E.processes.toList

/-! A blocking write is not allowed to move an event source inside the
Active region.  The wake base is the last settled view, so accepting such a
move would let a later NBA transition compare against a stale value and lose
an edge (§9.4.2). -/
def CoreMemProc.ndEventSources : CoreMemProc → List String
  | .edge p => p.clock :: p.reset.toList
  | .event events _ => events.map (·.signal)
  | _ => []

def CoreMemDesign.ndEventSources (E : CoreMemDesign) : List String :=
  E.processes.toList.flatMap CoreMemProc.ndEventSources

def CoreMemDesign.ndEventSourceChanged (E : CoreMemDesign) (before after : SvState) : Bool :=
  E.ndEventSources.any fun name => SvState.lookup before name != SvState.lookup after name

def CoreMemDesign.ndControlsKnownIn (E : CoreMemDesign) (view : SvState) : Bool :=
  E.ndEventSources.all fun name =>
    match SvState.lookup view name with
    | some value => value.bits.toList.all Logic.isKnown
    | none => false

def EdgeWork.isBlockingWrite : EdgeWork → Bool
  | .edgeStmt _ (.blockingAssign _ _) | .edgeStmt _ (.blockingAssignL _ _) => true
  | _ => false

/-- Move `fire i`: the `i`-th runnable cursor executes one parser node. -/
def NdState.fire (E : CoreMemDesign) (s : NdState) (i : Nat) : NdOutcome :=
  match pickAt i s.active with
  | none => .disabled
  | some (before, c, after) =>
      match c.work with
      | [] => .next { s with active := before ++ after }
      | head :: tail =>
          match head.ndOpen E s.store c.locals s.oracle with
          | .timeout => .refused "a reused leaf evaluator reported its internal budget"
          | .unsupported why => .refused why
          | .ok (r, exposed, o') =>
              if E.processes.toList.any
                  (CoreMemProc.firesIn (E.scalar.view s.store.scalar) (E.scalar.view r.state.scalar)) ||
                  (head.isBlockingWrite &&
                    E.ndEventSourceChanged (E.scalar.view s.store.scalar) (E.scalar.view r.state.scalar)) then
                .refused "9.4.2: a blocking write changes an event-source signal; intermediate update events are not modeled"
              else
                .next { store := r.state
                        active := before ++ EdgeCursor.keep ⟨exposed ++ tail, r.locals⟩ ++ after
                        scalarQ := s.scalarQ ++ r.scalarQ
                        memoryQ := s.memoryQ ++ r.memoryQ
                        base := s.base
                        oracle := o'
                        settled := false }

/-- Move `commit` (§4.5, §10.4.2): the Active set is empty; the queued
nonblocking updates are applied in issue order, and the processes whose
event occurs between the last wake view and the new view become runnable.
When none does, the slot is settled. -/
def NdState.commit (E : CoreMemDesign) (s : NdState) : NdOutcome :=
  match s.store.memory.commitNba s.memoryQ with
  | none => .refused "10.4.2: memory NBA commit lost its declaration identity"
  | some memory =>
      let scalar := E.scalarEdge.commit s.store.scalar s.scalarQ
      let store := E.normalizeScalar { s.store with scalar, memory } scalar
      let view := E.scalar.view store.scalar
      if !E.ndControlsKnownIn s.base || !E.ndControlsKnownIn view then
        .refused "9.4.2: x/z on a clock or event expression is outside the choice-explicit relation"
      else
        let woken := E.ndWake s.base view
        .next { store
                active := woken
                scalarQ := []
                memoryQ := []
                base := view
                oracle := s.oracle
                settled := woken.isEmpty }

/-- **The step function.**  Total, no fuel.  `choice` selects among the
runnable cursors; when none is runnable the only move is the NBA commit and
the choice is not consulted. -/
def CoreMemProc.ndClocked : CoreMemProc → Bool
  | .edge _ | .event _ _ => true
  | _ => false

def CoreMemDesign.ndAdmitted (E : CoreMemDesign) : Bool :=
  E.resolvedNets.isEmpty && E.readmemh.isEmpty && E.declInitializers.isEmpty &&
    E.processes.toList.all CoreMemProc.ndClocked

def ndStep (E : CoreMemDesign) (choice : Nat) (s : NdState) : NdOutcome :=
  if !E.ndAdmitted then .refused "the continuous-assignment and combinational regions are not in the choice-explicit relation yet"
  else if s.settled then .disabled
  else if s.active.isEmpty then s.commit E
  else s.fire E choice

/-- **The step relation**: `t` is produced by the step function for some
choice. -/
def Nd.Step (E : CoreMemDesign) (s t : NdState) : Prop := ∃ choice, ndStep E choice s = .next t

/-- **Runs**: finite chains of steps, of any length. -/
inductive Nd.Run (E : CoreMemDesign) : NdState → NdState → Prop where
  | refl (s : NdState) : Nd.Run E s s
  | tail {s t u : NdState} : Nd.Run E s t → Nd.Step E t u → Nd.Run E s u

theorem Nd.Run.single {E : CoreMemDesign} {s t : NdState} (h : Nd.Step E s t) : Nd.Run E s t :=
  .tail (.refl s) h

theorem Nd.Run.trans {E : CoreMemDesign} {s t u : NdState} (h₁ : Nd.Run E s t) (h₂ : Nd.Run E t u) :
    Nd.Run E s u := by
  induction h₂ with
  | refl => exact h₁
  | tail _ hstep ih => exact .tail ih hstep

theorem Nd.Run.head {E : CoreMemDesign} {s t u : NdState} (h₁ : Nd.Step E s t) (h₂ : Nd.Run E t u) :
    Nd.Run E s u := (Nd.Run.single h₁).trans h₂

/-- A settled state is terminal. -/
theorem Nd.Step.not_settled {E : CoreMemDesign} {s t : NdState} (h : Nd.Step E s t) :
    s.settled = false := by
  obtain ⟨i, hi⟩ := h
  cases hs : s.settled with
  | false => rfl
  | true =>
      cases hA : E.ndAdmitted <;> simp [ndStep, hs, hA] at hi

/-- A reachable refusal: some run from `s` reaches a state where some choice
is refused. -/
def Nd.Refuses (E : CoreMemDesign) (s : NdState) (why : String) : Prop :=
  ∃ t choice, Nd.Run E s t ∧ ndStep E choice t = .refused why

/-! ## One input event -/

/-! Time-zero processes are kept out until their ordering is modeled by an
explicit start-state relation. -/
/-- The state after the input row `entry` is applied to `st` (§4.5: the
inputs change, the processes waiting on them become runnable). -/
def NdState.begin (E : CoreMemDesign) (st : CoreMemState) (entry : SvState) (o : Oracle) :
    NdOutcome :=
  if E.ndAdmitted then
    let inputStore := E.scalar.applyInputs st.scalar entry
    let memoryInput := E.applyMemoryInputs entry st.memory
    let pre := E.normalizeScalar { st with memory := memoryInput } inputStore
    let before := E.scalar.view st.scalar
    let after := E.scalar.view pre.scalar
    if !E.ndControlsKnownIn before || !E.ndControlsKnownIn after then
      .refused "9.4.2: x/z on a clock or event expression is outside the choice-explicit relation"
    else
      .next { store := pre
              active := E.ndWake before after
              scalarQ := []
              memoryQ := []
              base := after
              oracle := o
              settled := false }
  else
    .refused "the continuous-assignment and combinational regions are not in the choice-explicit relation yet"

/-- **Event to settled.**  From the store `st`, the input row `entry` and the
oracle `o`, some run reaches the settled state `t`.  There is no bound on the
length of the run or on the number of NBA rounds. -/
def Nd.EventSettles (E : CoreMemDesign) (st : CoreMemState) (entry : SvState) (o : Oracle)
    (t : NdState) : Prop :=
  ∃ s₀, NdState.begin E st entry o = .next s₀ ∧ Nd.Run E s₀ t ∧ t.settled = true

/-- **Several input rows.**  `Nd.Trace E st o rows out o'`: from the store
`st` and the oracle `o` the rows are taken one at a time.  Each row leads to a
settled state by `Nd.EventSettles`; the next row starts from that state's
store and from the oracle that state left.  `out` lists the stores of the
settled states and `o'` is the oracle after the last row.  The oracle is
threaded: an answer consumed in one row is not offered again in a later one.
There is no bound on the number of rows or on the length of any run. -/
inductive Nd.Trace (E : CoreMemDesign) :
    CoreMemState → Oracle → List SvState → List CoreMemState → Oracle → Prop where
  | nil (st : CoreMemState) (o : Oracle) : Nd.Trace E st o [] [] o
  | cons {st : CoreMemState} {o o' : Oracle} {row : SvState} {t : NdState}
      {rest : List SvState} {out : List CoreMemState}
      (hrow : Nd.EventSettles E st row o t)
      (htail : Nd.Trace E t.store t.oracle rest out o') :
      Nd.Trace E st o (row :: rest) (t.store :: out) o'

/-! ## L1: invariants -/

/-- **L1.**  A property that holds at the start of a run and is preserved by
every step holds at the end of the run.  No bound on the length. -/
theorem Nd.Run.invariant {E : CoreMemDesign} {I : NdState → Prop}
    (hstep : ∀ s t, I s → Nd.Step E s t → I t) {s t : NdState} (h₀ : I s) (hr : Nd.Run E s t) : I t := by
  induction hr with
  | refl => exact h₀
  | tail _ hs ih => exact hstep _ _ ih hs

/-- L1 at the event level: an invariant established by `begin` holds in every
settled outcome. -/
theorem Nd.EventSettles.invariant {E : CoreMemDesign} {I : NdState → Prop}
    {st : CoreMemState} {entry : SvState} {o : Oracle} {t : NdState}
    (hinit : ∀ s₀, NdState.begin E st entry o = .next s₀ → I s₀)
    (hstep : ∀ s t, I s → Nd.Step E s t → I t)
    (h : Nd.EventSettles E st entry o t) : I t := by
  obtain ⟨s₀, hb, hr, -⟩ := h
  exact Nd.Run.invariant hstep (hinit s₀ hb) hr

/-! ## L3: a step that reads no unknown does not depend on the oracle -/

/-- Replace the oracle carried by an outcome. -/
def NdOutcome.withOracle (o : Oracle) : NdOutcome → NdOutcome
  | .next s => .next { s with oracle := o }
  | .refused why => .refused why
  | .disabled => .disabled

/-- The move `choice` consults no unknown: if it executes an `if` node, the
condition's four-state value has every bit known. -/
def NdState.ReadsKnown (E : CoreMemDesign) (s : NdState) (choice : Nat) : Prop :=
  ∀ before c after env cond yes no tail cv,
    pickAt choice s.active = some (before, c, after) →
    c.work = EdgeWork.edgeStmt env (.ifStmt cond yes no) :: tail →
    E.evalExprLocals env E.elems s.store (some 1) c.locals cond = .ok cv →
    cv.bits.toList.all Logic.isKnown = true

private def retag (o : Oracle) :
    Res (CoreMemExecResult × List EdgeWork × Oracle) → Res (CoreMemExecResult × List EdgeWork × Oracle)
  | .ok (r, exposed, _) => .ok (r, exposed, o)
  | .timeout => .timeout
  | .unsupported msg => .unsupported msg

private theorem ndLeaf_retag (E : CoreMemDesign) (st : CoreMemState) (locals : SvState)
    (o o' : Oracle) (env : IEnv) (stmt : PStmt) :
    ndLeaf E st locals o' env stmt = retag o' (ndLeaf E st locals o env stmt) := by
  unfold ndLeaf
  cases E.execStmtFuel env E.elems st locals 1 stmt <;> rfl

private theorem ndOpen_retag (E : CoreMemDesign) (st : CoreMemState) (locals : SvState)
    (o o' : Oracle) (w : EdgeWork)
    (hk : ∀ env cond yes no cv, w = .edgeStmt env (.ifStmt cond yes no) →
      E.evalExprLocals env E.elems st (some 1) locals cond = .ok cv →
      cv.bits.toList.all Logic.isKnown = true) :
    w.ndOpen E st locals o' = retag o' (w.ndOpen E st locals o) := by
  cases w with
  | edgeBlock env stmts => cases stmts <;> rfl
  | edgeLoop env name body values => cases values <;> rfl
  | edgeStmt env stmt =>
      cases stmt with
      | ifStmt cond yes no =>
          simp only [EdgeWork.ndOpen, ndOpenStmt]
          cases hcheck : E.ndCheckExpr cond with
          | timeout => simp [retag]
          | unsupported msg => simp [hcheck, retag]
          | ok u =>
              cases hc : E.evalExprLocals env E.elems st (some 1) locals cond with
              | timeout => simp [hcheck, hc, retag]
              | unsupported msg => simp [hcheck, hc, retag]
              | ok cv =>
                  have hkn := hk env cond yes no cv rfl hc
                  simp [hcheck, hc, retag, Oracle.read_known _ _ hkn]
      | forLoop name init cond step body =>
          simp only [EdgeWork.ndOpen, ndOpenStmt]
          cases forValues2 env name init cond step <;> rfl
      | block body => rfl
      | caseStmt subject items dflt mode check =>
          simp only [EdgeWork.ndOpen, ndOpenStmt]
          cases mode <;> rfl
      | unsupported kind text => rfl
      | blockingAssign target value =>
          simp only [EdgeWork.ndOpen, ndOpenStmt]
          cases hcheck : E.ndCheckExpr value with
          | timeout => simp [retag]
          | unsupported msg => simp [retag]
          | ok u => simpa [hcheck] using ndLeaf_retag E st locals o o' env _
      | blockingAssignL target value =>
          simp only [EdgeWork.ndOpen, ndOpenStmt]
          cases hcheck : E.ndCheckExpr value with
          | timeout => simp [hcheck, retag]
          | unsupported msg =>
              cases htarget : E.ndCheckTarget env st locals target <;> rfl
          | ok u =>
              cases htarget : E.ndCheckTarget env st locals target with
              | timeout => simp [retag]
              | unsupported msg => simp [retag]
              | ok v => simpa [hcheck, htarget] using ndLeaf_retag E st locals o o' env _
      | nbaAssign target value =>
          simp only [EdgeWork.ndOpen, ndOpenStmt]
          cases hcheck : E.ndCheckExpr value with
          | timeout => simp [retag]
          | unsupported msg => simp [retag]
          | ok u => simpa [hcheck] using ndLeaf_retag E st locals o o' env _
      | nbaAssignL target value =>
          simp only [EdgeWork.ndOpen, ndOpenStmt]
          cases hcheck : E.ndCheckExpr value with
          | timeout => simp [retag]
          | unsupported msg =>
              cases htarget : E.ndCheckTarget env st locals target <;> rfl
          | ok u =>
              cases htarget : E.ndCheckTarget env st locals target with
              | timeout => simp [retag]
              | unsupported msg => simp [retag]
              | ok v => simpa [hcheck, htarget] using ndLeaf_retag E st locals o o' env _
      | localDecl name width init =>
          simp only [EdgeWork.ndOpen, ndOpenStmt]
          cases hi : E.ndCheckOptionalExpr init <;> simp [hi, retag]
          exact ndLeaf_retag E st locals o o' env _
      | automaticDecl name width init =>
          simp only [EdgeWork.ndOpen, ndOpenStmt]
          cases hi : E.ndCheckOptionalExpr init <;> simp [hi, retag]
          exact ndLeaf_retag E st locals o o' env _

/-- **L3.**  If the move `choice` reads no unknown, the step function gives
the same outcome under any oracle, and the oracle passes through unchanged.
So for such a step the oracle is a bystander: it can be replaced by any other
supply, before or after the step. -/
theorem ndStep_oracle_irrelevant {E : CoreMemDesign} {s : NdState} {choice : Nat}
    (h : s.ReadsKnown E choice) (o' : Oracle) :
    ndStep E choice { s with oracle := o' } = (ndStep E choice s).withOracle o' := by
  cases hA : E.ndAdmitted with
  | false => simp [ndStep, hA, NdOutcome.withOracle]
  | true =>
    simp only [ndStep, hA, Bool.false_eq_true, ↓reduceIte]
    cases hs : s.settled with
    | true => simp [NdOutcome.withOracle]
    | false =>
        cases ha : s.active.isEmpty with
        | true =>
            simp only [Bool.false_eq_true, ↓reduceIte, NdState.commit]
            cases s.store.memory.commitNba s.memoryQ <;> simp [NdOutcome.withOracle]
            split <;> simp [NdOutcome.withOracle]
        | false =>
            simp only [Bool.false_eq_true, ↓reduceIte, NdState.fire]
            cases hp : pickAt choice s.active with
            | none => simp [NdOutcome.withOracle]
            | some r =>
                obtain ⟨before, c, after⟩ := r
                cases hw : c.work with
                | nil => simp [hw, hs, NdOutcome.withOracle]
                | cons head tail =>
                    have hk : ∀ env cond yes no cv, head = .edgeStmt env (.ifStmt cond yes no) →
                        E.evalExprLocals env E.elems s.store (some 1) c.locals cond = .ok cv →
                        cv.bits.toList.all Logic.isKnown = true := by
                      intro env cond yes no cv hhead hc
                      exact h before c after env cond yes no tail cv hp (by rw [hw, hhead]) hc
                    simp only [hw]
                    rw [ndOpen_retag E s.store c.locals s.oracle o' head hk]
                    cases head.ndOpen E s.store c.locals s.oracle with
                    | timeout => simp [retag, NdOutcome.withOracle]
                    | unsupported msg => simp [retag, NdOutcome.withOracle]
                    | ok r =>
                        obtain ⟨r, exposed, o1⟩ := r
                        simp only [retag]
                        by_cases hblock : head.isBlockingWrite = true
                        · simp [hblock]
                          split <;> simp [NdOutcome.withOracle]
                        · simp [hblock]
                          split <;> simp [NdOutcome.withOracle]

/-- L3, second half: a step that reads no unknown leaves the oracle as it
was. -/
theorem ndStep_oracle_unchanged {E : CoreMemDesign} {s t : NdState} {choice : Nat}
    (h : s.ReadsKnown E choice) (hstep : ndStep E choice s = .next t) : t.oracle = s.oracle := by
  have h' := ndStep_oracle_irrelevant h s.oracle
  have hs : ({ s with oracle := s.oracle } : NdState) = s := rfl
  rw [hs, hstep] at h'
  simp only [NdOutcome.withOracle, NdOutcome.next.injEq] at h'
  have := congrArg NdState.oracle h'
  simpa using this

/-! ## Totality and repeated unknown reads

An unsettled state always has a move for choice zero, either a successor or a
named refusal.  The only states without a successor or refusal are settled
states.
-/
theorem ndStep_zero_not_disabled {E : CoreMemDesign} {s : NdState} (h : s.settled = false) :
    ndStep E 0 s ≠ .disabled := by
  intro hd
  cases hA : E.ndAdmitted with
  | false => simp [ndStep, hA] at hd
  | true =>
    simp only [ndStep, hA, Bool.false_eq_true, ↓reduceIte] at hd
    simp only [h, Bool.false_eq_true, ↓reduceIte] at hd
    cases ha : s.active with
    | nil =>
        simp only [ha, List.isEmpty_nil, ↓reduceIte, NdState.commit] at hd
        cases hmem : s.store.memory.commitNba s.memoryQ with
        | none => simp [hmem] at hd
        | some memory =>
            simp [hmem] at hd
            split at hd <;> simp_all
    | cons c rest =>
        simp only [ha, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, NdState.fire, pickAt] at hd
        repeat' split at hd
        all_goals simp at hd

/-! The same unknown decision can resolve differently at two reads. -/
theorem ndOpenStmt_if_unknown_twice (E : CoreMemDesign) (st : CoreMemState) (locals : SvState)
    (env : IEnv) (cond : PExpr) (yes : PStmt) (no : Option PStmt)
    (h : E.evalExprLocals env E.elems st (some 1) locals cond = .ok ⟨#[Logic.lx]⟩)
    (hobs : ndXObserver? cond = none) (o : Oracle) :
    ndOpenStmt E st locals (Oracle.cons true (Oracle.cons false o)) env (.ifStmt cond yes no) =
        .ok (.idle st locals, [EdgeWork.edgeStmt env yes], Oracle.cons false o) ∧
      ndOpenStmt E st locals (Oracle.cons false o) env (.ifStmt cond yes no) =
        .ok (.idle st locals, no.toList.map (EdgeWork.edgeStmt env), o) := by
  constructor <;>
    simp [ndOpenStmt, CoreMemDesign.ndCheckExpr, h, hobs, Oracle.read, Oracle.bits,
      Logic.isKnown, LVec.condTrue] <;> decide

#print axioms Oracle.read_xread
#print axioms Oracle.read_complete
#print axioms Oracle.read_known
#print axioms Oracle.zero_read_condTrue
#print axioms Nd.Step.not_settled
#print axioms Nd.Run.invariant
#print axioms Nd.EventSettles.invariant
#print axioms ndStep_oracle_irrelevant
#print axioms ndStep_oracle_unchanged
#print axioms ndStep_zero_not_disabled
#print axioms ndOpenStmt_if_unknown_twice

end LeanModels.Sv.Kernel
