import LeanModels.Sv.Ingest2
import LeanModels.Sv.SeqCycleStages

/-!
# A register file on the ordinary E route, at every depth `N ≥ 2`, over every run

The census design `sem2/unpacked_cpuregs_e`, the PicoRV32-shaped register file:

```systemverilog
module unpacked_cpuregs_e #(parameter int N = 32) (input logic clk, input logic [4:0] raddr, input logic [4:0] waddr,
    input logic [31:0] wdata, input logic we, output logic [31:0] rdata);
  logic [31:0] cpuregs [0:N-1];
  always_ff @(posedge clk) begin
    if (we) cpuregs[waddr] <= wdata;
  end
  assign rdata = cpuregs[raddr];
endmodule
```

The memory is an indexed family, never cells: its contents are a function of the label (the memory view), its next
contents ONE write equation (`memWrite`), its read ONE read equation (`memRd`). An address with an x/z bit, or one at or
beyond `N`, selects nothing: a read gives all x, a write writes nothing (IEEE 1800-2023 §11.5.1, the route's
`MemShape.index?`, here `rfIdx`); a `we` that does not read 1 (0, x, z) writes nothing (E's `if` reads `condTrue`).

1. **Structure** (`rf_structure`, `sv_structure`): the instantiation at every `2 ≤ N < 2^30`, in the clocked profile
   (one memory, 4-state, not a port), with the obligations.
2. **The cycle equations** (`rf_cycle`): one cycle is `rfF`: the pre sample reads the memory before the edge, the post
   memory is the write equation under `we`, the post sample reads the written memory.
3. **The claim over every run** (`rf_runs`), from every coherent state (memory contents arbitrary: the x start and every
   power-up), on every typed stimulus: the write equation and the read equation in every cycle, the low slot writing
   nothing, and READ AFTER WRITE: a write of `d` at a known address `a < N` with `we = 1` in cycle `c` is read back by a
   read of `a` in the pre sample of cycle `c + 1`; a read of another known address `b < N` shows the contents `b` had
   before the write; a cycle whose `we` does not read 1, or whose write address has an x/z bit, leaves the memory as it
   was.

Oracle: Icarus Verilog 12.0 (stable), a testbench outside the repository (1024 rows at N = 2, 5, 32: the cycle
equations and the claim's clauses on 4-state `we`, addresses with x/z bits, addresses at or beyond `N`, and the x start;
0 mismatches; a testbench model that writes when `we` is x is caught, 274 mismatches).
-/

open LeanModels.Sv LeanModels.Sv.Kernel

namespace Examples.«system-verilog».seq_cycle.rf_proof

set_option maxRecDepth 100000 in
load_design_sv2 rf from "Examples/system-verilog/sem2/unpacked_cpuregs_e/unpacked_cpuregs_e.sv.json"

-- The instantiation at every depth, computed once (`rf.mirror`, `rf.mirror_eq`); the stages below read it.
set_option maxHeartbeats 1000000 in
seq_mirror (N : Nat) (h1 : 2 ≤ N) (h2 : N < 2 ^ 30) : rf.e N

-- A run on the route at `N = 4` (compiled): write 5 at 1, read 1 (shows 5), write 9 at 7 (out of range: nothing),
-- read 1 again, write with an x address (nothing), read 1.
#guard (match rf.e 4 with
  | .ok E => match runCoreMemRows E E.initial (cycleRows "clk"
      [[("raddr", .ofNat 5 1), ("waddr", .ofNat 5 1), ("wdata", .ofNat 32 5), ("we", .ofNat 1 1)],
       [("raddr", .ofNat 5 1), ("waddr", .ofNat 5 7), ("wdata", .ofNat 32 9), ("we", .ofNat 1 1)],
       [("raddr", .ofNat 5 1), ("waddr", LVec.lit "x0000"), ("wdata", .ofNat 32 3), ("we", .ofNat 1 1)],
       [("raddr", .ofNat 5 1), ("waddr", .ofNat 5 1), ("wdata", .ofNat 32 3), ("we", .ofNat 1 0)]]) with
    | .ok rows => rows.map (fun st => SvState.showSignal (CoreMemState.view E st) "rdata") ==
        ["xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx", "00000000000000000000000000000101",
         "00000000000000000000000000000101", "00000000000000000000000000000101",
         "00000000000000000000000000000101", "00000000000000000000000000000101",
         "00000000000000000000000000000101", "00000000000000000000000000000101"]
    | _ => false
  | _ => false)

/-! ## 1. Structure and interface -/

set_option maxHeartbeats 1000000 in
theorem rf_structure (N : Nat) (h1 : 2 ≤ N) (h2 : N < 2 ^ 30) : SeqDesign (rf.e N) "clk" := by
  sv_structure

set_option maxHeartbeats 1000000 in
theorem rf_ports (N : Nat) (h1 : 2 ≤ N) (h2 : N < 2 ^ 30) :
    SeqPorts (rf.e N) [("clk", 1), ("raddr", 5), ("waddr", 5), ("wdata", 32), ("we", 1)] [("rdata", 32)] := by
  sv_interface

/-! ## 2. The cycle equations -/

/-- **The address decision** of the route (`MemShape.index?` of `[0:N-1]`): a known address below `N` selects its
label; an address with an x/z bit, or one at or beyond `N`, selects nothing. -/
def rfIdx (N : Nat) (a : LVec) : Option Int :=
  match a.toNat? with
  | some k => if k < N then some (k : Int) else none
  | none => none

/-- The route's index decision on the declared range `[0:N-1]` is `rfIdx`. -/
theorem rf_index {N : Nat} (h : 2 ≤ N) {m : MemShape} (h0 : m.msb = 0) (h1 : m.lsb = (N : Int) - 1) (a : LVec) :
    m.index? false a = rfIdx N a := by
  unfold MemShape.index? rfIdx
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases a.toNat? with
  | none => rfl
  | some k =>
      simp only [Option.map_some]
      by_cases hk : k < N
      · have : m.inRange (k : Int) := by unfold MemShape.inRange; right; omega
        simp [this, hk]
      · have : ¬ m.inRange (k : Int) := by unfold MemShape.inRange; omega
        simp [this, hk]

/-- The view of the design, in declaration order. -/
def view (c ra wa wd we rd : LVec) : SvState :=
  [("clk", c), ("raddr", ra), ("waddr", wa), ("wdata", wd), ("we", we), ("rdata", rd)]

/-- A signal of a view. -/
def lk (v : SvState) (n : String) : LVec := (SvState.lookup v n).getD ⟨#[]⟩

/-- **The cycle function**: the applied inputs; the pre sample reads the memory before the edge (the low slot writes
nothing); the post memory is the write equation when `we` reads 1; the post sample reads the post memory. -/
def rfF (N : Nat) (σ : SvState × MemV) (dt : SvState) : (SvState × MemV) × (SvState × MemV) :=
  let ra := appliedIn dt σ.1 "raddr"
  let wa := appliedIn dt σ.1 "waddr"
  let wd := appliedIn dt σ.1 "wdata"
  let we := appliedIn dt σ.1 "we"
  let m' := if we.condTrue then memWrite σ.2 "cpuregs" (rfIdx N wa) wd else σ.2
  ((view ⟨#[.l0]⟩ ra wa wd we (memRd σ.2 "cpuregs" (rfIdx N ra) 32), σ.2),
   (view ⟨#[.l1]⟩ ra wa wd we (memRd m' "cpuregs" (rfIdx N ra) 32), m'))

/-- The states the cycle keeps: the view's shape with its widths, every memory element 32 bits wide. -/
def RfInv (σ : SvState × MemV) : Prop :=
  ∃ c ra wa wd we rd, σ.1 = view c ra wa wd we rd ∧ c.width = 1 ∧ ra.width = 5 ∧ wa.width = 5 ∧ wd.width = 32 ∧
    we.width = 1 ∧ rd.width = 32 ∧ ∀ k, (σ.2 "cpuregs" k).width = 32

theorem memRd_width32 {mv : MemV} (h : ∀ k, (mv "cpuregs" k).width = 32) (k? : Option Int) :
    (memRd mv "cpuregs" k? 32).width = 32 := seqE_memRd_width h k?

theorem memWrite_width32 {mv : MemV} (h : ∀ k, (mv "cpuregs" k).width = 32) {k? : Option Int} {x : LVec}
    (hx : x.width = 32) (k : Int) : (memWrite mv "cpuregs" k? x "cpuregs" k).width = 32 := by
  unfold memWrite
  split
  · exact hx
  · exact h k

theorem rfF_inv {N : Nat} {σ : SvState × MemV} {dt : SvState} (hm : ∀ k, (σ.2 "cpuregs" k).width = 32)
    (hra : (appliedIn dt σ.1 "raddr").width = 5) (hwa : (appliedIn dt σ.1 "waddr").width = 5)
    (hwd : (appliedIn dt σ.1 "wdata").width = 32) (hwe : (appliedIn dt σ.1 "we").width = 1) :
    RfInv (rfF N σ dt).2 := by
  have hm' : ∀ k, ((if (appliedIn dt σ.1 "we").condTrue = true then
      memWrite σ.2 "cpuregs" (rfIdx N (appliedIn dt σ.1 "waddr")) (appliedIn dt σ.1 "wdata") else σ.2) "cpuregs" k).width
        = 32 := by
    intro k
    split
    · exact memWrite_width32 hm hwd k
    · exact hm k
  exact ⟨_, _, _, _, _, _, rfl, rfl, hra, hwa, hwd, hwe, memRd_width32 hm' _, hm'⟩

set_option maxHeartbeats 4000000 in
/-- **The cycle equations**: from every state of the shape, on every typed data entry, the route's cycle is `rfF`, and
the post state keeps the shape. -/
theorem rf_cycle (N : Nat) (h1 : 2 ≤ N) (h2 : N < 2 ^ 30) {E : CoreMemDesign} (hE : rf.e N = .ok E)
    (σ : SvState × MemV) (dt : SvState) (hσ : RfInv σ) (hd : E.DataTyped "clk" dt) :
    E.cycleMV "clk" σ dt = .ok (rfF N σ dt) ∧ RfInv (rfF N σ dt).2 := by
  obtain ⟨E', hE', hP, -⟩ := rf_structure N h1 h2
  rw [hE] at hE'
  cases hE'
  obtain ⟨v, mv⟩ := σ
  obtain ⟨c, ra, wa, wd, we, rd, hv, hc, hra, hwa, hwd, hwe, hrd, hmw⟩ := hσ
  dsimp only at hv hmw
  subst hv
  have hE0 : rf.mirror N = E := Res.ok.inj ((rf.mirror_eq N h1 h2).symm.trans hE)
  -- the applied inputs and their widths
  have hshape : E.ShapeV (view c ra wa wd we rd) := by
    subst hE0; simp [rf.mirror_def, CoreMemDesign.ShapeV, view, hc, hra, hwa, hwd, hwe, hrd]
  have hdi : E.dataInputs "clk" = ["raddr", "waddr", "wdata", "we"] := by
    subst hE0; simp [rf.mirror_def, CoreMemDesign.dataInputs, Elab.toDesign2, Design2.inputNames]
  have hwidth : ∀ n w x, n ∈ E.dataInputs "clk" → E.scalar.toDesign2.declWidth n = some w →
      SvState.lookup (view c ra wa wd we rd) n = some x → x.width = w →
      (appliedIn dt (view c ra wa wd we rd) n).width = w :=
    fun n w x hn hw hx hxw => CoreMemDesign.appliedIn_width hd hn hw hx hxw
  have hra' := hwidth "raddr" 5 ra (by simp [hdi]) (by subst hE0; simp [rf.mirror_def, Elab.toDesign2, Design2.declWidth])
    (by simp [view, SvState.lookup]) hra
  have hwa' := hwidth "waddr" 5 wa (by simp [hdi]) (by subst hE0; simp [rf.mirror_def, Elab.toDesign2, Design2.declWidth])
    (by simp [view, SvState.lookup]) hwa
  have hwd' := hwidth "wdata" 32 wd (by simp [hdi]) (by subst hE0; simp [rf.mirror_def, Elab.toDesign2, Design2.declWidth])
    (by simp [view, SvState.lookup]) hwd
  have hwe' := hwidth "we" 1 we (by simp [hdi]) (by subst hE0; simp [rf.mirror_def, Elab.toDesign2, Design2.declWidth])
    (by simp [view, SvState.lookup]) hwe
  refine ⟨?_, rfF_inv hmw hra' hwa' hwd' hwe'⟩
  rw [CoreMemDesign.cycleMV_applied hP mv hshape dt, CoreMemDesign.appliedEntry, hdi]
  simp only [List.map_cons, List.map_nil]
  unfold rfF
  generalize appliedIn dt (view c ra wa wd we rd) "raddr" = ra' at hra' ⊢
  generalize appliedIn dt (view c ra wa wd we rd) "waddr" = wa' at hwa' ⊢
  generalize appliedIn dt (view c ra wa wd we rd) "wdata" = wd' at hwd' ⊢
  generalize appliedIn dt (view c ra wa wd we rd) "we" = we' at hwe' ⊢
  sv_seq_cycle hcyc : E.cycleMV "clk" (view c ra wa wd we rd, mv)
      [("raddr", ra'), ("waddr", wa'), ("wdata", wd'), ("we", we')] using hE0
    [rf.mirror_def, view, hc, hra, hwa, hwd, hwe, hrd, hra', hwa', hwd', hwe', hmw]
  rw [hcyc]
  simp only [rf_index h1, view]
  -- the post read is the read of the post memory (one decision, `we`)
  split <;> simp_all [memRd_memWrite]

/-! ## 3. The claim, over every run -/

/-- **The register file's claim** about the samples of a run (pre and post of each cycle, each a view and a memory
view): the write equation, the low slot writing nothing, the read equation before and after the edge. -/
def RfClaim (N : Nat) (tr : List ((SvState × MemV) × (SvState × MemV))) : Prop :=
  ∀ (c : Nat) (pc : (SvState × MemV) × (SvState × MemV)), tr[c]? = some pc →
    -- the write equation: the edge writes `wdata` at the resolved address when `we` reads 1
    pc.2.2 = (if (lk pc.1.1 "we").condTrue then
      memWrite pc.1.2 "cpuregs" (rfIdx N (lk pc.1.1 "waddr")) (lk pc.1.1 "wdata") else pc.1.2) ∧
    -- the low slot writes nothing: the cycle starts from the previous cycle's memory
    (∀ pp, tr[c - 1]? = some pp → 1 ≤ c → pc.1.2 = pp.2.2) ∧
    -- the read equation, before and after the edge
    lk pc.1.1 "rdata" = memRd pc.1.2 "cpuregs" (rfIdx N (lk pc.1.1 "raddr")) 32 ∧
    lk pc.2.1 "rdata" = memRd pc.2.2 "cpuregs" (rfIdx N (lk pc.2.1 "raddr")) 32

/-- The state before cycle `c ≥ 1` of a run is the post sample of cycle `c - 1`. -/
theorem prev_cycle (N : Nat) (σ : SvState × MemV) (ins : List SvState) (c : Nat)
    (pp : (SvState × MemV) × (SvState × MemV)) (hc : 1 ≤ c) (hpp : (runF (rfF N) σ ins)[c - 1]? = some pp) :
    stF (rfF N) σ ins c = pp.2 := by
  rw [runF_getElem?] at hpp
  cases hin : ins[c - 1]? with
  | none => simp [hin] at hpp
  | some d =>
      simp only [hin, Option.map_some, Option.some.injEq] at hpp
      subst hpp
      obtain ⟨k, rfl⟩ : ∃ k, c = k + 1 := ⟨c - 1, by omega⟩
      exact stF_succ (rfF N) σ ins k d (by simpa using hin)

/-- **The claim from the cycle function**, cycle by cycle. -/
theorem rfClaim_of_runF (N : Nat) (σ : SvState × MemV) (ins : List SvState) : RfClaim N (runF (rfF N) σ ins) := by
  intro c pc hpc
  have hpc' := hpc
  rw [runF_getElem?] at hpc
  cases hin : ins[c]? with
  | none => simp [hin] at hpc
  | some dt =>
      simp only [hin, Option.map_some, Option.some.injEq] at hpc
      subst hpc
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [rfF, lk, view, SvState.lookup]
      · intro pp hpp hc
        rw [show (rfF N (stF (rfF N) σ ins c) dt).1.2 = (stF (rfF N) σ ins c).2 from rfl,
          prev_cycle N σ ins c pp hc hpp]
      · simp [rfF, lk, view, SvState.lookup]
      · simp [rfF, lk, view, SvState.lookup]

/-! ### What the claim says about a register file's use: read after write -/

theorem rfIdx_ofBitVec {N : Nat} (a : BitVec 5) (h : a.toNat < N) : rfIdx N (LVec.ofBitVec a) = some (a.toNat : Int) := by
  simp [rfIdx, h]

/-- **READ AFTER WRITE**: a write of `wdata` at a known address `a < N` with `we = 1` in cycle `c` is read back by a read
of `a` in the pre sample of cycle `c + 1`. -/
theorem rf_read_after_write {N : Nat} {tr : List ((SvState × MemV) × (SvState × MemV))} (h : RfClaim N tr)
    {c : Nat} {pc pc' : (SvState × MemV) × (SvState × MemV)} (hc : tr[c]? = some pc) (hc' : tr[c + 1]? = some pc')
    {a : BitVec 5} (hwe : lk pc.1.1 "we" = LVec.ofBitVec 1#1) (hwa : lk pc.1.1 "waddr" = LVec.ofBitVec a)
    (hN : a.toNat < N) (hra : lk pc'.1.1 "raddr" = LVec.ofBitVec a) : lk pc'.1.1 "rdata" = lk pc.1.1 "wdata" := by
  obtain ⟨hw, -, -, -⟩ := h c pc hc
  obtain ⟨-, hlow, hrd, -⟩ := h (c + 1) pc' hc'
  rw [hrd, hra, hlow pc (by simpa using hc) (by omega), hw, hwe, hwa, rfIdx_ofBitVec a hN]
  simp [memRd, memWrite]

/-- **The other cells keep their contents**: after a write at `a`, a read of another known address `b < N` in the next
cycle shows what `b` held before the write. -/
theorem rf_read_other {N : Nat} {tr : List ((SvState × MemV) × (SvState × MemV))} (h : RfClaim N tr)
    {c : Nat} {pc pc' : (SvState × MemV) × (SvState × MemV)} (hc : tr[c]? = some pc) (hc' : tr[c + 1]? = some pc')
    {a b : BitVec 5} (hwa : lk pc.1.1 "waddr" = LVec.ofBitVec a) (hba : b ≠ a) (hbN : b.toNat < N)
    (hrb : lk pc'.1.1 "raddr" = LVec.ofBitVec b) : lk pc'.1.1 "rdata" = pc.1.2 "cpuregs" (b.toNat : Int) := by
  obtain ⟨hw, -, -, -⟩ := h c pc hc
  obtain ⟨-, hlow, hrd, -⟩ := h (c + 1) pc' hc'
  have hne : rfIdx N (LVec.ofBitVec a) ≠ some (b.toNat : Int) := by
    unfold rfIdx
    simp only [LVec.toNat?_ofBitVec]
    split
    · intro he
      simp only [Option.some.injEq, Int.natCast_inj] at he
      exact hba (BitVec.eq_of_toNat_eq he.symm)
    · simp
  rw [hrd, hrb, hlow pc (by simpa using hc) (by omega), hw, hwa, rfIdx_ofBitVec b hbN]
  split <;> simp [memRd, memWrite, hne]

/-- **No write without `we = 1`**: a cycle whose `we` reads 0, x or z leaves the memory as it was. -/
theorem rf_no_write {N : Nat} {tr : List ((SvState × MemV) × (SvState × MemV))} (h : RfClaim N tr)
    {c : Nat} {pc : (SvState × MemV) × (SvState × MemV)} (hc : tr[c]? = some pc)
    (hwe : (lk pc.1.1 "we").condTrue = false) : pc.2.2 = pc.1.2 := by
  obtain ⟨hw, -, -, -⟩ := h c pc hc
  rw [hw, hwe]
  rfl

/-- **No write at an x/z address**: a cycle whose write address has an x or z bit leaves the memory as it was. -/
theorem rf_x_address {N : Nat} {tr : List ((SvState × MemV) × (SvState × MemV))} (h : RfClaim N tr)
    {c : Nat} {pc : (SvState × MemV) × (SvState × MemV)} (hc : tr[c]? = some pc)
    (hwa : (lk pc.1.1 "waddr").toNat? = none) : pc.2.2 = pc.1.2 := by
  obtain ⟨hw, -, -, -⟩ := h c pc hc
  have hnone : rfIdx N (lk pc.1.1 "waddr") = none := by simp [rfIdx, hwa]
  rw [hw, hnone, memWrite_none]
  split <;> rfl

set_option maxHeartbeats 1000000 in
/-- **THE CLAIM**: in every run of the route, from every coherent state (memory contents arbitrary), on every typed
stimulus. -/
theorem rf_runs (N : Nat) (h1 : 2 ≤ N) (h2 : N < 2 ^ 30) : SeqRunsM (rf.e N) "clk" (RfClaim N) := by
  obtain ⟨E, hE, hP, hO⟩ := rf_structure N h1 h2
  have hE0 : rf.mirror N = E := Res.ok.inj ((rf.mirror_eq N h1 h2).symm.trans hE)
  refine SeqRunsM.of_cycleFn hE hP hO (by subst hE0; simp [rf.mirror_def, Elab.toDesign2, Design2.declWidth]) RfInv ?_
    (rfF N) (fun σ dt hσ hd => rf_cycle N h1 h2 hE σ dt hσ hd)
    (fun σ ins _ _ => rfClaim_of_runF N σ ins)
  intro st hc hmc
  have hs := hc.shape
  have hms := CoreMemDesign.MemCoherent.shape hP.mems hmc
  obtain ⟨hk, hw⟩ := hs
  generalize E.scalar.view st.scalar = v at hk hw ⊢
  generalize E.memOf st.memory = mv at hms ⊢
  subst hE0
  simp [rf.mirror_def, CoreMemDesign.MemShapeV] at hms
  rcases v with _ | ⟨⟨n1, x1⟩, _ | ⟨⟨n2, x2⟩, _ | ⟨⟨n3, x3⟩, _ | ⟨⟨n4, x4⟩, _ | ⟨⟨n5, x5⟩, _ | ⟨⟨n6, x6⟩,
    _ | ⟨_, _⟩⟩⟩⟩⟩⟩⟩ <;> simp [rf.mirror_def] at hk hw
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩ := hk
  refine ⟨x1, x2, x3, x4, x5, x6, rfl, hw.1, hw.2.1, hw.2.2.1, hw.2.2.2.1, hw.2.2.2.2.1, hw.2.2.2.2.2, ?_⟩
  intro k
  exact hms k

/-- **READ AFTER WRITE, over every run**: in every run of the route, from every coherent state, on every typed
stimulus, a write of `wdata` at a known address `a < N` with `we = 1` is read back in the next cycle's pre sample, and a
read of another known address `b < N` there shows what `b` held before the write. -/
theorem rf_runs_raw (N : Nat) (h1 : 2 ≤ N) (h2 : N < 2 ^ 30) :
    SeqRunsM (rf.e N) "clk" fun tr => ∀ (c : Nat) (pc pc' : (SvState × MemV) × (SvState × MemV)) (a : BitVec 5),
      tr[c]? = some pc → tr[c + 1]? = some pc' → lk pc.1.1 "waddr" = LVec.ofBitVec a → a.toNat < N →
      (lk pc.1.1 "we" = LVec.ofBitVec 1#1 → lk pc'.1.1 "raddr" = LVec.ofBitVec a →
        lk pc'.1.1 "rdata" = lk pc.1.1 "wdata") ∧
      (∀ b : BitVec 5, b ≠ a → b.toNat < N → lk pc'.1.1 "raddr" = LVec.ofBitVec b →
        lk pc'.1.1 "rdata" = pc.1.2 "cpuregs" (b.toNat : Int)) :=
  (rf_runs N h1 h2).mono fun _ h c pc pc' a hc hc' hwa hN =>
    ⟨fun hwe hra => rf_read_after_write h hc hc' hwe hwa hN hra,
     fun b hba hbN hrb => rf_read_other h hc hc' hwa hba hbN hrb⟩

#print axioms rf_structure
#print axioms rf_ports
#print axioms rf_cycle
#print axioms rf_read_after_write
#print axioms rf_read_other
#print axioms rf_no_write
#print axioms rf_x_address
#print axioms rf_runs
#print axioms rf_runs_raw

end Examples.«system-verilog».seq_cycle.rf_proof
