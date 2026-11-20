import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleStages

/-!
# The route's time-zero state on the clocked profile

The route's time-zero state (`CoreMemDesign.initialState`) quiesces the continuous-assign region over
the declaration-initialized state `CoreMemDesign.initial` (the x start: every variable x, every net z), IEEE 1800-2023
§4.5 and §10.3. On a design whose continuous assign drives a value other than its target's x/z start the two states
differ, so the clocked theory states the time-zero state as that settled route result (`initialState_of_quiet`,
`SeqProfileI.initialState`), and as a fixpoint under the topological obligation (`SeqProfileI.initialState_settled`).

The design is the semantics lane's receipt `sem2/initial_quiet_assign`, loaded as it is:

```systemverilog
module initial_quiet_assign(output logic y);
  assign y = 1'b1;
endmodule
```

Oracle: the receipt's own (`sem2/initial_quiet_assign/check.py`): Icarus Verilog 13.0 and Xcelium 24.03-s004 report
`y=1`. No further oracle result is claimed here.
-/

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».seq_cycle.seq_time_zero

load_design_sv2 qa from "Examples/system-verilog/sem2/initial_quiet_assign/initial_quiet_assign.sv.json"

-- The instantiation, computed once (`qa.mirror`, `qa.mirror_eq`, `qa.mirror_def`).
seq_mirror : qa.e

/-- The design is in the instant profile, with its obligations. -/
theorem qa_structure : SeqDesignI qa.e := by
  sv_structure

/-- **The time-zero state**: it exists, `y = 1` there (the x start has `y = x`), and it is coherent with a coherent
memory, so every run claim over coherent start states holds from it. -/
theorem qa_time_zero : ∃ E, qa.e = .ok E ∧ ∃ st, E.initialState = .ok st ∧
    E.scalar.view st.scalar = [("y", LVec.ofNat 1 1)] ∧ E.Coherent st ∧ E.MemCoherent st.memory := by
  obtain ⟨E, hE, hP, hO⟩ := qa_structure
  refine ⟨E, hE, ?_⟩
  have hE0 := hE
  sv_seq_use [qa.mirror_eq, qa.mirror_def] at hE0
  have hdi : E.declInitializers = [] := by
    subst hE0
    rfl
  have hrm : E.readmemh = [] := by subst hE0; rfl
  have hv : E.settleV (E.memOf E.initial.memory) (E.scalar.view E.initial.scalar) = .ok [("y", LVec.ofNat 1 1)] := by
    subst hE0; rfl
  obtain ⟨st, hs, hvs, -, hc, hmc⟩ :=
    hP.initialState (CoreMemDesign.seqOblI_spec hO).2.1 hrm hdi hv
  exact ⟨st, hs, hvs, hc, hmc⟩

/-- **The time-zero state is settled**: one more pass changes nothing, and the route's continuous-assign region run
from it keeps `y = 1`. -/
theorem qa_time_zero_settled : ∃ E, qa.e = .ok E ∧ ∃ st, E.initialState = .ok st ∧
    E.scalar.view st.scalar = [("y", LVec.ofNat 1 1)] ∧
    ∃ st', E.settleCanonical E.env E.elems st E.processes.toList = .ok st' ∧
      E.scalar.view st'.scalar = [("y", LVec.ofNat 1 1)] := by
  obtain ⟨E, hE, hP, hO⟩ := qa_structure
  refine ⟨E, hE, ?_⟩
  have hE0 := hE
  sv_seq_use [qa.mirror_eq, qa.mirror_def] at hE0
  have hdi : E.declInitializers = [] := by
    subst hE0
    rfl
  have hrm : E.readmemh = [] := by subst hE0; rfl
  have hv : E.settleV (E.memOf E.initial.memory) (E.scalar.view E.initial.scalar) = .ok [("y", LVec.ofNat 1 1)] := by
    subst hE0; rfl
  obtain ⟨st, hs, hvs, -, st', hs', hv'⟩ :=
    hP.initialState_settled (CoreMemDesign.seqOblI_spec hO).2.1 hrm hdi hv
  exact ⟨st, hs, hvs, st', hs', hv'⟩

/-- **The time-zero state is not the x start** here: the statement the clocked theory made before the route's
time-zero settle (`initialState = .ok initial`) is false on this design. -/
theorem qa_not_initial : ∃ E, qa.e = .ok E ∧ E.initialState ≠ .ok E.initial := by
  obtain ⟨E, hE, st, hs, hvs, -, -⟩ := qa_time_zero
  refine ⟨E, hE, fun h => ?_⟩
  rw [hs] at h
  cases h
  have hE0 := hE
  sv_seq_use [qa.mirror_eq, qa.mirror_def] at hE0
  subst hE0
  revert hvs
  decide

#print axioms qa_structure
#print axioms qa_time_zero
#print axioms qa_time_zero_settled
#print axioms qa_not_initial

/-! ## A clocked example's runs from both start states

The examples' run claims hold from every coherent start state, so from the time-zero state too, and their concrete runs
start from the x start. For each clocked example whose design has a continuous assign (`shreg_proof`, `rf_proof`,
`valid_proof`, `amem_proof`), the route's samples of that example's own concrete run are the same from the time-zero
state as from the x start (compiled checks, at the examples' parameter points). On `seq_mem/async_mem_fifo`
(`amem_proof.lean`; `assign q = mem[0]`, `q` a net) the two start states differ (`q` is z at the x start and x at time
zero). -/

/-- The route's samples of `rows` from the time-zero state are those from the x start. -/
def sameFromBoth (r : Res CoreMemDesign) (rows : List SvState) : Bool :=
  match r with
  | .ok E => match E.initialState with
    | .ok st0 => match runCoreMemRows E st0 rows, runCoreMemRows E E.initial rows with
      | .ok a, .ok b => a.map (CoreMemState.view E) == b.map (CoreMemState.view E)
      | _, _ => false
    | _ => false
  | _ => false

set_option maxRecDepth 100000 in
load_design_sv2 shreg from "Examples/system-verilog/sem2/packed_shift_canonical_e/packed_shift_canonical_e.sv.json"
set_option maxRecDepth 100000 in
load_design_sv2 rf from "Examples/system-verilog/sem2/unpacked_cpuregs_e/unpacked_cpuregs_e.sv.json"
set_option maxRecDepth 100000 in
load_design_sv2 vc from "Examples/system-verilog/seq_valid_chain/valid_chain_profile.sv.json"
set_option maxRecDepth 100000 in
load_design_sv2 am from "Examples/system-verilog/seq_mem/async_mem_fifo.sv.json"

-- `shreg_proof`'s run at `N = 4`.
#guard sameFromBoth (shreg.e 4) (cycleRows "clk" [[("v", .ofNat 1 1)], [("v", .ofNat 1 0)]])

-- `rf_proof`'s run at `N = 4`.
#guard sameFromBoth (rf.e 4) (cycleRows "clk"
  [[("raddr", .ofNat 5 1), ("waddr", .ofNat 5 1), ("wdata", .ofNat 32 5), ("we", .ofNat 1 1)],
   [("raddr", .ofNat 5 1), ("waddr", .ofNat 5 7), ("wdata", .ofNat 32 9), ("we", .ofNat 1 1)],
   [("raddr", .ofNat 5 1), ("waddr", LVec.lit "x0000"), ("wdata", .ofNat 32 3), ("we", .ofNat 1 1)],
   [("raddr", .ofNat 5 1), ("waddr", .ofNat 5 1), ("wdata", .ofNat 32 3), ("we", .ofNat 1 0)]])

-- `valid_proof`'s run at `W = 8`.
#guard sameFromBoth (vc.e 8) (cycleRows "clk"
  [[("rst", .ofNat 1 1), ("valid_i", .ofNat 1 0), ("ready_i", .ofNat 1 0), ("data_i", .ofNat 8 0)],
   [("rst", .ofNat 1 0), ("valid_i", .ofNat 1 1), ("ready_i", .ofNat 1 1), ("data_i", .ofNat 8 0x5a)],
   [("rst", .ofNat 1 0), ("valid_i", .ofNat 1 0), ("ready_i", .ofNat 1 0), ("data_i", .ofNat 8 0xff)],
   [("rst", .ofNat 1 0), ("valid_i", .ofNat 1 1), ("ready_i", .ofNat 1 1), ("data_i", .ofNat 8 0x3c)]])

-- `amem_proof`'s design at `W = N = 4` (reset, load 9, load 3): the start states differ, the samples do not.
#guard sameFromBoth (am.e 4 4) (cycleRows "clk" [[("rstn", .ofNat 1 0), ("d", .ofNat 4 5)],
  [("rstn", .ofNat 1 1), ("d", .ofNat 4 9)], [("rstn", .ofNat 1 1), ("d", .ofNat 4 3)]])
#guard (match am.e 4 4 with
  | .ok E => match E.initialState with
    | .ok st0 =>
      let rows := cycleRows "clk" [[("rstn", .ofNat 1 0), ("d", .ofNat 4 5)], [("rstn", .ofNat 1 1), ("d", .ofNat 4 9)],
        [("rstn", .ofNat 1 1), ("d", .ofNat 4 3)]]
      match runCoreMemRows E st0 rows, runCoreMemRows E E.initial rows with
      | .ok a, .ok b =>
          CoreMemState.view E st0 != CoreMemState.view E E.initial &&
          SvState.showSignal (CoreMemState.view E E.initial) "q" == "zzzz" &&
          SvState.showSignal (CoreMemState.view E st0) "q" == "xxxx" &&
          a.map (CoreMemState.view E) == b.map (CoreMemState.view E) &&
          (cyclePairs a).map (fun pp => SvState.showSignal (CoreMemState.view E pp.2) "q") ==
            ["0000", "1001", "0011"]
      | _, _ => false
    | _ => false
  | _ => false)

end Examples.«system-verilog».seq_cycle.seq_time_zero
