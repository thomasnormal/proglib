import LeanModels.Sv.Ingest2
import LeanModels.Sv.Kernel.NdStep

/-!
# Rows on the arms of the choice-explicit step (`ndStep`, `begin`, `fire`, `commit`)

Twenty-three concrete rows on the loaded `simultaneous_nba` design, one per
behaviour of the step function that a statement relies on: the refusals by
name, the two schedules of the swap, a choice out of range, an `if` on an
unknown under two oracles, and what the executor does on the same inputs.
They were first run as probes by the T2 review; here they are part of the
build.

Two kinds of row, and the difference matters:

* `theorem R<n> ... := by decide +kernel`: the row is checked by the Lean
  KERNEL (no axiom beyond the kernel's own reduction).  These are the rows
  that do not evaluate a right-hand side or a condition: admission, `begin`,
  the commit refusal, choice out of range, the syntactic observer refusal.
* `#guard`: the row is EVALUATED by Lean's compiled evaluator, not by the
  kernel.  The kernel does not reduce the reused expression evaluator
  (`evalExprLocals`) on a concrete store, so every row that executes an
  assignment or an `if` condition is of this kind.  A `#guard` fails the
  build when the value differs; it is not a theorem.  The kernel-checked
  statements about the same behaviours are in `relation.lean`
  (`swap_only`, `swap_exists`, `step_rise`, `swap_step_sound_run`,
  `if_condition_x_read_twice_can_differ`).

No simulator was run for any row.  No oracle (simulator) result is claimed
here; differential rows through the simulator gate are separate work.

Row R18 records a KNOWN GAP, not intended behaviour: an x observer inside a
write-target index is not refused yet (the value check sees a known index).
The row changes when the observer walk covers write-target indices.
-/

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».sem2.simultaneous_nba.step_rows

load_design_sv2 sn from "Examples/system-verilog/sem2/simultaneous_nba/simultaneous_nba.sv.json"

def E : CoreMemDesign := match sn.e with | .ok d => d | _ => default

set_option maxRecDepth 100000

def bit (b : Logic) : LVec := ⟨#[b]⟩

def view (ca cb a b : Logic) : SvState :=
  [("clk_a", bit ca), ("clk_b", bit cb), ("a", bit a), ("b", bit b)]

inductive Seen where
  | next (settled : Bool) (active queued : Nat) (view : SvState)
  | refused (why : String)
  | disabled
  deriving DecidableEq, Repr

def seen : NdOutcome → Seen
  | .next s => .next s.settled s.active.length s.scalarQ.length (E.scalar.view s.store.scalar)
  | .refused why => .refused why
  | .disabled => .disabled

def seenR : Res CoreMemState → Option SvState
  | .ok s => some (E.scalar.view s.scalar)
  | _ => none

def runC (s : NdState) : List Nat → NdOutcome
  | [] => .next s
  | c :: cs => match ndStep E c s with | .next t => runC t cs | o => o

def fromBegin (o : NdOutcome) (cs : List Nat) : NdOutcome :=
  match o with | .next s => runC s cs | o => o

def cur (ss : List PStmt) : EdgeCursor := { work := ss.map (EdgeWork.edgeStmt E.env) }

def mk (st : CoreMemState) (cs : List EdgeCursor) (o : Oracle := Oracle.zero) : NdState :=
  { store := st, active := cs, scalarQ := [], memoryQ := [], base := E.scalar.view st.scalar,
    oracle := o, settled := false }

def low : SvState := [("clk_a", bit .l0), ("clk_b", bit .l0)]
def rise : SvState := [("clk_a", bit .l1), ("clk_b", bit .l1)]

def pre (st : CoreMemState) (entry : SvState) : CoreMemState :=
  E.normalizeScalar { st with memory := E.applyMemoryInputs entry st.memory }
    (E.scalar.applyInputs st.scalar entry)

def st0 : CoreMemState := pre E.initial low
def st01 : CoreMemState := E.normalizeScalar E.initial (E.storeFromView (view .l0 .l0 .l0 .l1))
def st11 : CoreMemState := pre E.initial rise

def xControl : String :=
  "9.4.2: x/z on a clock or event expression is outside the choice-explicit relation"
def blockingSource : String :=
  "9.4.2: a blocking write changes an event-source signal; intermediate update events are not modeled"

/-- The state of row R6: the power-on store, nobody woken, an empty wake base. -/
def s6 : NdState :=
  { store := E.initial
    active := E.ndWake [] []
    scalarQ := []
    memoryQ := []
    base := []
    oracle := Oracle.zero
    settled := false }

def ifA : PStmt := .ifStmt (.ident "a") (.nbaAssign "b" (.int 1)) (some (.nbaAssign "b" (.int 0)))

/-! ## Stores used by the rows -/

/-- Both clocks 0, `a` and `b` x. -/
theorem st0_view : E.scalar.view st0.scalar = view .l0 .l0 .lx .lx := by decide +kernel

/-- Both clocks 0, `a = 0`, `b = 1`. -/
theorem st01_view : E.scalar.view st01.scalar = view .l0 .l0 .l0 .l1 := by decide +kernel

/-! ## From the power-on store: the executor answers, the relation refuses -/

/-- R1. The executor's preparation accepts the power-on store (clocks x). -/
theorem R1 : (match E.prepareStep E.initial [] with | .ok _ => true | _ => false) = true := by
  decide +kernel

/-- R2. `begin` refuses the power-on store on an empty row: x on a control. -/
theorem R2 : seen (NdState.begin E E.initial [] Oracle.zero) = .refused xControl := by
  decide +kernel

/-- R3. `begin` refuses the power-on store when both clocks rise: x on a
control in the old view. -/
theorem R3 : seen (NdState.begin E E.initial rise Oracle.zero) = .refused xControl := by
  decide +kernel

/- R4 (evaluated). The executor answers the same row: it counts x -> 1 as an
edge and leaves `a`, `b` x. -/
#guard seenR (E.step E.initial rise) = some (view .l1 .l1 .lx .lx)

/-- R5. The executor's in-slot loop returns with empty before/after views. -/
theorem R5 : seenR (E.edgeQuiesce 1 E.initial [] [] E.initial) = some (view .lx .lx .lx .lx) := by
  decide +kernel

/-- R6. The relation's only move from the corresponding state is the
control-x refusal of the commit. -/
theorem R6 : seen (ndStep E 0 s6) = .refused xControl := by decide +kernel

/-! ## The swap from known clocks: both schedules, and the executor -/

/-- R7. `begin` from known clocks wakes both processes. -/
theorem R7 : seen (NdState.begin E st01 rise Oracle.zero) =
    .next false 2 0 (view .l1 .l1 .l0 .l1) := by decide +kernel

/- R8 (evaluated). Schedule `a <= b` first, then `b <= a`, then the commit:
settled, `(a, b) = (1, 0)`. -/
#guard seen (fromBegin (NdState.begin E st01 rise Oracle.zero) [0, 0, 0]) =
  .next true 0 0 (view .l1 .l1 .l1 .l0)

/- R9 (evaluated). The other schedule: the same settled view. -/
#guard seen (fromBegin (NdState.begin E st01 rise Oracle.zero) [1, 0, 0]) =
  .next true 0 0 (view .l1 .l1 .l1 .l0)

/- R10 (evaluated). The executor's result on the same row is that view. -/
#guard seenR (E.step st01 rise) = some (view .l1 .l1 .l1 .l0)

/-- R11. A choice that names no runnable cursor is disabled. -/
theorem R11 : seen (fromBegin (NdState.begin E st01 rise Oracle.zero) [2]) = .disabled := by
  decide +kernel

/-! ## Two hand-built cursors that interfere: the order shows

These two rows are why uniqueness is stated from a footprint condition and
never for all states: two blocking writes to one signal settle differently
under the two schedules. -/

/- R12 (evaluated). `a = 0` then `a = 1`: `a` ends 1. -/
#guard seen (runC (mk st0 [cur [.blockingAssign "a" (.int 0)], cur [.blockingAssign "a" (.int 1)]])
  [0, 0, 0]) = .next true 0 0 (view .l0 .l0 .l1 .lx)

/- R13 (evaluated). The other order: `a` ends 0. -/
#guard seen (runC (mk st0 [cur [.blockingAssign "a" (.int 0)], cur [.blockingAssign "a" (.int 1)]])
  [1, 0, 0]) = .next true 0 0 (view .l0 .l0 .l0 .lx)

/-! ## The named refusals -/

/-- R14. An x observer (`===`) in an `if` condition is refused by name. -/
theorem R14 : seen (runC (mk st0 [cur [.ifStmt (.binary .ceq (.ident "a") (.ident "a"))
    (.nbaAssign "a" (.int 1)) none]]) [0]) =
    .refused "12.4: case equality '===' is outside per-read x semantics" := by decide +kernel

/- R15 (evaluated). A blocking write that raises a clock is refused. -/
#guard seen (runC (mk st0 [cur [.blockingAssign "clk_a" (.int 1)]]) [0]) = .refused blockingSource

/- R16 (evaluated). The stale-wake-base shape `clk_a = 0; clk_a <= 1` from
`clk_a = 1` is refused at the blocking write. -/
#guard seen (runC (mk st11 [cur [.blockingAssign "clk_a" (.int 0), .nbaAssign "clk_a" (.int 1)]])
  [0, 0, 0]) = .refused blockingSource

/- R17 (evaluated). A write whose index is unknown is refused. -/
#guard seen (runC (mk st0 [cur [.blockingAssignL (.bitSel "a" (.ident "b")) (.int 1)]]) [0]) =
  .refused "11.5.1: unknown write index is outside per-read x semantics"

/- R18 (evaluated). KNOWN GAP: an x observer inside a write-target index is
NOT refused; the step answers. -/
#guard seen (runC (mk st01 [cur [.blockingAssignL
  (.bitSel "a" (.binary .ceq (.ident "b") (.ident "b"))) (.int 1)]]) [0]) =
  .next false 0 0 (view .l0 .l0 .l0 .l1)

/- R23 (evaluated). A nonblocking write of x to a clock: the commit refuses,
x on a control. -/
#guard seen (runC (mk st0 [cur [.nbaAssign "clk_a" (.ident "a")]]) [0, 0]) = .refused xControl

/-! ## An unknown at an `if` condition, and unknowns elsewhere -/

/- R19 (evaluated). `if (a) b <= 1; else b <= 0;` with `a` x, under the
always-0 oracle: the else branch, `b = 0`. -/
#guard seen (runC (mk st0 [cur [ifA]]) [0, 0, 0]) = .next true 0 0 (view .l0 .l0 .lx .l0)

/- R20 (evaluated). The same under the always-1 oracle: the then branch,
`b = 1`. -/
#guard seen (runC (mk st0 [cur [ifA]] (fun _ => true)) [0, 0, 0]) =
  .next true 0 0 (view .l0 .l0 .lx .l1)

/- R21 (evaluated). A ternary on x is the four-state merge: `b` is x, no
oracle answer is taken. -/
#guard seen (runC (mk st0 [cur [.blockingAssign "b" (.ternary (.ident "a") (.int 1) (.int 0))]])
  [0, 0]) = .next true 0 0 (view .l0 .l0 .lx .lx)

/- R22 (evaluated). x read twice in ONE expression, `b = a ^ a`, under the
always-1 oracle: `b` is x.  Operand reads are not oracle sites. -/
#guard seen (runC (mk st0 [cur [.blockingAssign "b" (.binary (.m0 .xor) (.ident "a") (.ident "a"))]]
  (fun _ => true)) [0, 0]) = .next true 0 0 (view .l0 .l0 .lx .lx)

#print axioms R1
#print axioms R2
#print axioms R3
#print axioms R5
#print axioms R6
#print axioms R7
#print axioms R11
#print axioms R14

end Examples.«system-verilog».sem2.simultaneous_nba.step_rows
