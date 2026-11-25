import LeanModels.Sv.Kernel.CoreMemExec
import LeanModels.Sv.SeqCycleObl
import LeanModels.Sv.SeqFamily

/-!
# Source-shaped memory combinational lemmas

These are the reusable equations for a one-rank unpacked memory whose
continuous targets are retained as `PLhs.arrayElem`.  They do not lower a
memory into scalar cells: writes and reads remain `MemState` operations, and
the packed readback is a proof-side view built from the native cells.
-/

namespace LeanModels.Sv.Kernel

open LeanModels.Sv

namespace MemState

theorem read_after_cell_write {s : MemState} {name : String} {k : Int}
    {v : LVec} {m : MemBlock} (hm : s.lookup name = some m)
    (hin : m.shape.inRange k) (hv : v.width = m.shape.elemWidth) :
    (s.write name k v).bind (fun s' => s'.read name k) =
      some (m.shape.convert v) := by
  exact MemState.read_write_same hm hin hv

theorem read_other_after_cell_write {s : MemState} {name : String} {k j : Int}
    {v : LVec} {m : MemBlock} (hm : s.lookup name = some m)
    (hjk : j ≠ k) (hv : v.width = m.shape.elemWidth) :
    (s.write name k v).bind (fun s' => s'.read name j) = s.read name j := by
  exact MemState.read_write_other hm hjk hv

theorem distinct_cell_writes_read_commute {s : MemState} {name : String} {k j q : Int}
    {v w : LVec} {m : MemBlock} (hm : s.lookup name = some m)
    (hjk : j ≠ k) (hv : v.width = m.shape.elemWidth)
    (hw : w.width = m.shape.elemWidth) :
    ((s.write name k v).bind (fun s' => s'.write name j w)).bind
        (fun s' => s'.read name q) =
      ((s.write name j w).bind (fun s' => s'.write name k v)).bind
        (fun s' => s'.read name q) := by
  exact MemState.read_two_writes_comm_of_distinct hm hjk hv hw

end MemState

/-- The packed proof-side image of `n` one-rank memory cells.  The native
memory remains the source of each cell value; this is not a semantic
lowering. -/
def MemState.readPacked (s : MemState) (name : String) (W n : Nat) (base : LVec) : LVec :=
  LVec.insertEntries W (fun r => (s.read name (r : Int)).getD (LVec.xVec W)) n base

theorem MemState.readPacked_ofBitVec {W n : Nat} {bits : Nat → BitVec W} {s : MemState}
    {name : String} {base : LVec} (hbase : base.width = n * W)
    (hread : ∀ r : Nat, r < n → s.read name (r : Int) = some (LVec.ofBitVec (bits r))) :
    s.readPacked name W n base = LVec.ofBitVec (packBV W n bits) := by
  have hinsert : ∀ m, m ≤ n →
      LVec.insertEntries W (fun r => (s.read name (r : Int)).getD (LVec.xVec W)) m base =
      LVec.insertEntries W (fun r => LVec.ofBitVec (bits r)) m base := by
    intro m hm
    induction m with
    | zero => rfl
    | succ m ih =>
        rw [LVec.insertEntries_succ, LVec.insertEntries_succ, ih (by omega)]
        congr 1
        rw [hread m (by omega)]
        rfl
  rw [show s.readPacked name W n base =
      LVec.insertEntries W (fun r => (s.read name (r : Int)).getD (LVec.xVec W)) n base by rfl]
  rw [hinsert n (by omega)]
  exact LVec.insertEntries_ofBitVec bits base hbase

theorem CoreMemDesign.memory_settle_fixpoint {E : CoreMemDesign} {v v' : SvState} {mv : MemV}
    (htopo : E.topoC = true) (hv : E.matV v = v)
    (h : E.settleV mv v = .ok v') : E.settleV mv v' = .ok v' := by
  exact CoreMemDesign.settleV_idem htopo hv h

end LeanModels.Sv.Kernel
