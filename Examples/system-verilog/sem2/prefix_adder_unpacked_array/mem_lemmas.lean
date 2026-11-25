import LeanModels.Sv.MemCombLemmas

namespace Examples.«system-verilog».sem2.prefix_adder_unpacked_array.mem_lemmas

open LeanModels.Sv
open LeanModels.Sv.Kernel

private def prefixMemDecl : PDecl :=
  { name := "mem", type := .packed [] (some 1),
    unpackedDims := [{ msb := .int 1, lsb := .int 0 }] }

private def prefixMemShape : MemShape :=
  { name := "mem", elemWidth := 1, msb := 1, lsb := 0 }

private def prefixMemElab : Elab :=
  { name := "prefix_mem", decls := #[
      { name := "a", width := 1, isInput := true },
      { name := "y", width := 1, isOutput := true }], procs := #[] }

private def prefixMemDesign : CoreMemDesign :=
  { name := "prefix_mem", env := {}, elems := [("a", 1), ("y", 1)],
    scalar := prefixMemElab,
    scalarEdge := { decls := prefixMemElab.decls, procs := #[], name := prefixMemElab.name },
    memories := #[{ source := prefixMemDecl, shape := prefixMemShape }],
    processes := #[
      .assign (.arrayElem "mem" [.int 0]) (.ident "a"),
      .assign (.ident "y") (.arrayElem "mem" [.int 0])] }

#guard prefixMemDesign.memories.size == 1
#guard prefixMemDesign.topoC

theorem prefixMem_shape_lookup :
    (prefixMemDesign.initial.memory.lookup "mem").map (·.shape) = some prefixMemShape := by
  rfl

private def prefixMemInput (b : Logic) : CoreMemState :=
  prefixMemDesign.setScalarState prefixMemDesign.initial "a" (LVec.ofLogic b)

private def prefixMemSettled (b : Logic) : Res CoreMemState :=
  prefixMemDesign.settleAssign prefixMemDesign.env prefixMemDesign.elems
    (prefixMemInput b) prefixMemDesign.processes.toList

#guard match prefixMemSettled .l0 with
  | .ok st => st.memory.read "mem" 0 == some (LVec.ofLogic .l0) &&
      SvState.lookup (CoreMemState.view prefixMemDesign st) "y" == some (LVec.ofLogic .l0)
  | _ => false

#guard match prefixMemSettled .l1 with
  | .ok st => st.memory.read "mem" 0 == some (LVec.ofLogic .l1) &&
      SvState.lookup (CoreMemState.view prefixMemDesign st) "y" == some (LVec.ofLogic .l1)
  | _ => false

theorem prefixMem_packed_readback {bits : Nat → BitVec 1} {base : LVec}
    (hbase : base.width = 2)
    (h0 : prefixMemDesign.initial.memory.read "mem" 0 = some (LVec.ofBitVec (bits 0)))
    (h1 : prefixMemDesign.initial.memory.read "mem" 1 = some (LVec.ofBitVec (bits 1))) :
    MemState.readPacked prefixMemDesign.initial.memory "mem" 1 2 base =
      LVec.ofBitVec (packBV 1 2 bits) := by
  apply MemState.readPacked_ofBitVec hbase
  intro r hr
  rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl
  · exact h0
  · exact h1


theorem prefixMem_distinct_cell_writes {v w : LVec} {q : Int}
    (hv : LVec.width v = 1) (hw : LVec.width w = 1) :
    ((MemState.write prefixMemDesign.initial.memory "mem" 0 v).bind
        (fun s' => MemState.write s' "mem" 1 w)).bind
        (fun s' => MemState.read s' "mem" q) =
      ((MemState.write prefixMemDesign.initial.memory "mem" 1 w).bind
        (fun s' => MemState.write s' "mem" 0 v)).bind
        (fun s' => MemState.read s' "mem" q) := by
  apply MemState.distinct_cell_writes_read_commute
  · rfl
  · omega
  · exact hv
  · exact hw

end Examples.«system-verilog».sem2.prefix_adder_unpacked_array.mem_lemmas
