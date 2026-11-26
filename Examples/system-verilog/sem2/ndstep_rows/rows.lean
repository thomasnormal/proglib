import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.NdStep

open LeanModels.Sv LeanModels.Sv.Kernel
namespace Examples.«system-verilog».sem2.ndstep_rows

load_design_sv2 sn from
  "Examples/system-verilog/sem2/simultaneous_nba/simultaneous_nba.sv.json"
def E : CoreMemDesign := match sn.e with | .ok d => d | _ => default

def bit (b : Logic) : LVec := ⟨#[b]⟩
def cur (ss : List PStmt) : EdgeCursor := { work := ss.map (EdgeWork.edgeStmt E.env) }
def pre (st : CoreMemState) (entry : SvState) : CoreMemState :=
  E.normalizeScalar { st with memory := E.applyMemoryInputs entry st.memory }
    (E.scalar.applyInputs st.scalar entry)
def mk (st : CoreMemState) (cs : List EdgeCursor) (o : Oracle := Oracle.zero) : NdState :=
  { store := st, active := cs, scalarQ := [], memoryQ := [],
    base := E.scalar.view st.scalar, oracle := o, settled := false }
def storeOf (st : CoreMemState) : NdOutcome → CoreMemState
  | .next s => s.store
  | _ => st
def runC (s : NdState) : List Nat → NdOutcome
  | [] => .next s
  | c :: cs => match ndStep E c s with | .next t => runC t cs | o => o
def low : SvState := [("clk_a", bit .l0), ("clk_b", bit .l0)]
def rise : SvState := [("clk_a", bit .l1), ("clk_b", bit .l1)]
def st0 : CoreMemState := pre E.initial low
def st01 : CoreMemState :=
  storeOf st0 (runC (mk st0 [cur [.blockingAssign "a" (.int 0),
    .blockingAssign "b" (.int 1)]]) [0, 0, 0])
def viewBit (s : CoreMemState) (name : String) : Option Logic :=
  (E.scalar.view s.scalar).lookup name |>.bind (·.bits[0]?)
def nextView (o : NdOutcome) (name : String) (value : Logic) : Bool :=
  match o with
  | .next s => viewBit s.store name == some value
  | _ => false
def refused (o : NdOutcome) (why : String) : Bool :=
  match o with
  | .refused actual => actual == why
  | _ => false
def outcomeTag : NdOutcome → String
  | .next _ => "next"
  | .refused _ => "refused"
  | .disabled => "disabled"
def allOneIf : NdState :=
  { mk st0 [cur [.ifStmt (.ident "a")
      (.nbaAssign "b" (.int 1)) (some (.nbaAssign "b" (.int 0)))]] with
    oracle := fun _ => true }
def allOneXor : NdState :=
  { mk st0 [cur [.blockingAssign "b"
      (.binary (.m0 .xor) (.ident "a") (.ident "a"))]] with
    oracle := fun _ => true }

#guard E.ndAdmitted

/-! R7: `begin` creates both runnable edge cursors for a known rising row. -/
#guard match NdState.begin E st01 rise Oracle.zero with
  | .next s => s.active.length == 2 && s.settled == false
  | _ => false

/-! R8 and R9: both legal cursor schedules settle at the swap. -/
#guard match NdState.begin E st01 rise Oracle.zero with
  | .next s =>
      match runC s [0, 0, 0] with
      | .next t => t.settled && nextView (.next t) "a" .l1 && nextView (.next t) "b" .l0
      | _ => false
  | _ => false
#guard match NdState.begin E st01 rise Oracle.zero with
  | .next s =>
      match runC s [1, 0, 0] with
      | .next t => t.settled && nextView (.next t) "a" .l1 && nextView (.next t) "b" .l0
      | _ => false
  | _ => false

/-! R10: the executor's source-shaped swap row returns the same settled view. -/
#guard match E.step st01 rise with
  | .ok t => viewBit t "a" == some .l1 && viewBit t "b" == some .l0
  | _ => false

/-! R11: an out-of-range schedule choice is disabled. -/
#guard match NdState.begin E st01 rise Oracle.zero with
  | .next s => match ndStep E 2 s with | .disabled => true | _ => false
  | _ => false

/-! R12 and R13 are the deliberately non-confluent hand-built race rows. -/
#guard match runC (mk st0 [cur [.blockingAssign "a" (.int 0)],
    cur [.blockingAssign "a" (.int 1)]]) [0, 0, 0] with
  | .next s => viewBit s.store "a" == some .l1
  | _ => false
#guard match runC (mk st0 [cur [.blockingAssign "a" (.int 0)],
    cur [.blockingAssign "a" (.int 1)]]) [1, 0, 0] with
  | .next s => viewBit s.store "a" == some .l0
  | _ => false

/-! R14-R17: named refusal rows. -/
#guard refused (runC (mk st0 [cur [.ifStmt
    (.binary .ceq (.ident "a") (.ident "a"))
    (.nbaAssign "a" (.int 1)) none]]) [0])
  "12.4: case equality '===' is outside per-read x semantics"
#guard refused (runC (mk st0 [cur [.blockingAssign "clk_a" (.int 1)]]) [0])
  "9.4.2: a blocking write changes an event-source signal; intermediate update events are not modeled"
#guard refused (runC (mk (pre E.initial rise)
    [cur [.blockingAssign "clk_a" (.int 0), .nbaAssign "clk_a" (.int 1)]]) [0, 0, 0])
  "9.4.2: a blocking write changes an event-source signal; intermediate update events are not modeled"
#guard refused (runC (mk st0 [cur [.blockingAssignL
    (.bitSel "a" (.ident "b")) (.int 1)]]) [0])
  "11.5.1: unknown write index is outside per-read x semantics"

/-! R18 is retained as an executable gap row until the target-index observer
walk is added.  It currently reaches the leaf evaluator. -/
#eval outcomeTag (runC (mk st01 [cur [.blockingAssignL
  (.bitSel "a" (.binary .ceq (.ident "b") (.ident "b"))) (.int 1)]]) [0])

/-! R19 and R20: the oracle selects opposite branches at an unknown `if`. -/
#guard match runC (mk st0 [cur [.ifStmt (.ident "a")
    (.nbaAssign "b" (.int 1)) (some (.nbaAssign "b" (.int 0)))]] ) [0, 0, 0] with
  | .next s => viewBit s.store "b" == some .l0
  | _ => false
#guard match runC allOneIf [0, 0, 0] with
  | .next s => viewBit s.store "b" == some .l1
  | _ => false

/-! R21 and R22: ternary and operand x reads remain on the four-state merge. -/
#guard match runC (mk st0 [cur [.blockingAssign "b"
    (.ternary (.ident "a") (.int 1) (.int 0))]]) [0, 0] with
  | .next s => viewBit s.store "b" == some .lx
  | _ => false
#guard match runC allOneXor [0, 0] with
  | .next s => viewBit s.store "b" == some .lx
  | _ => false

/-! R23: commit rejects an x control value. -/
#guard refused (runC (mk st0 [cur [.nbaAssign "clk_a" (.ident "a")]]) [0, 0])
  "9.4.2: x/z on a clock or event expression is outside the choice-explicit relation"

end Examples.«system-verilog».sem2.ndstep_rows
